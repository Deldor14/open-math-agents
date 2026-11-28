"""Verify upper volumes for the even-sheet, one-high-coordinate torus body.

No solver or third-party library is used. Run: python3 verify.py
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from math import factorial, prod
from pathlib import Path
import json

BASE = Fraction(551449, 10**6)
ROOT = Path(__file__).resolve().parent


def types_and_sizes(dimension, mesh):
    half = mesh // 2
    low_types = list(combinations_with_replacement(range(half), dimension))
    other_low = combinations_with_replacement(range(half), dimension - 1)
    high_types = [rest + (high,) for rest in other_low for high in range(half, 3*mesh//4)]
    types = low_types + high_types
    sizes = [factorial(dimension) // prod(factorial(v) for v in Counter(t).values())
             for t in types]
    return types, sizes


def constraint_rows(dimension, mesh, types):
    """Yield (coefficients, twice the right-hand side) in certificate order."""
    count = len(types)
    for index in range(count):
        yield {index: 1, count + index: -1}, 1
    type_index = {key: i for i, key in enumerate(types)}
    half, end = mesh // 2, 3*mesh // 4
    for rest in combinations_with_replacement(range(half), dimension - 2):
        diagonals = [[] for _ in range(2*end)]
        for first in range(end):
            for second in range(end):
                if min(first, second) >= half:
                    continue
                key = tuple(sorted(rest + (first, second)))
                diagonals[first + second].append(type_index[key])
        for left in range(half - 1, mesh + 1):
            for right in range(left, mesh + 1):
                row = Counter(i for s in range(left, right) for i in diagonals[s])
                for edge in (left - 1, right):
                    row.update(count + i for i in diagonals[edge])
                twice_rhs = (right - left + 1)*mesh
                twice_capacity = sum(v*(2 if i < count else 1) for i, v in row.items())
                if twice_capacity > twice_rhs:
                    yield row, twice_rhs


def check_certificate(dimension, mesh):
    data = json.loads((ROOT / f'base-d{dimension}-k{mesh}.json').read_text())
    assert data['d'] == dimension and data['k'] == mesh
    scale = data['scale']
    assert isinstance(scale, int) and scale > 0
    multipliers = dict(data['dual'])
    assert len(multipliers) == len(data['dual'])
    assert all(isinstance(i, int) and i >= 0 and isinstance(w, int) and w >= 0
               for i, w in multipliers.items())
    types, sizes = types_and_sizes(dimension, mesh)
    count = len(types)
    residual = [scale*s for s in sizes] + [0]*count
    twice_cost = 0
    for index, (row, twice_rhs) in enumerate(constraint_rows(dimension, mesh, types)):
        weight = multipliers.pop(index, 0)
        twice_cost += weight*twice_rhs
        for column, coefficient in row.items():
            residual[column] -= weight*coefficient
    assert not multipliers
    twice_cost += 2*sum(max(0, v) for v in residual[:count])
    twice_cost += sum(max(0, v) for v in residual[count:])
    volume = Fraction(twice_cost, 4*scale*mesh**dimension)
    assert volume < BASE**dimension
    print(f'd={dimension:2d}, mesh={mesh:2d}, upper volume={volume}')


def raw_volume(dimension):
    return Fraction(dimension + 2, 2**(dimension + 2))


if __name__ == '__main__':
    # Compare BASE with sqrt((17-6sqrt(2))/28) without floating point.
    delta = 17 - 28*BASE**2
    assert delta > 0 and delta**2 > 72
    for d in (1, 2, 3, 15):
        assert raw_volume(d) < BASE**d
    assert raw_volume(16)/raw_volume(15) < BASE
    # For d >= 15 the successive ratio (d+3)/(2d+4) decreases.
    for d in range(4, 15):
        check_certificate(d, 12 if 8 <= d <= 10 else 8)
