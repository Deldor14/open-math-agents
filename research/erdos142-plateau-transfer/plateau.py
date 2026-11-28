"""Deterministic grid transfer for the dyadic plateau profile in zeemy23 #180978."""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
import sys


def import_engine(path):
    sys.path.insert(0, str(Path(path).resolve()))
    import construct
    import features
    return construct, features


def progression_free(n, sites):
    """Square the indicator polynomial using carry-free base-256 blocks."""
    word = max(1, (n.bit_length() + 7) // 8)
    data = bytearray((n + 1) * word)
    for x in sites:
        data[x * word] = 1
    value = int.from_bytes(data, 'little')
    square = (value * value).to_bytes((2 * n + 1) * word, 'little')
    return all(int.from_bytes(square[2*x*word:(2*x+1)*word], 'little') == 1 for x in sites)


def digit_witness(n):
    """Pad with zero in the translated radix-182 certificate by wonsukchoi, #181852."""
    published = (1, 3, 26, 29, 34, 40, 45, 48, 59, 71, 75, 81, 85, 86, 90, 96,
                 100, 112, 118, 123, 126, 137, 142, 145, 157, 168, 173, 180)
    digits = [x-1 for x in published]
    offsets = [0]
    place = 1
    while place < n:
        offsets = [offset + place*d for d in digits for offset in offsets if offset + place*d < n]
        place *= 182
    return [x+1 for x in offsets]


class Plateau:
    def __init__(self, m):
        from verifica_parametro import J, V
        self.m = m
        self.n = (m - 1).bit_length()
        self.eps = Q(1, 128*m)
        self.gamma = Q(1, m*(self.n+2))
        self.knots = [V - (V-J) / (1 << i) for i in range(self.n + 1)]
        self.cusps = [Q(1, 2) + t for t in [*self.knots, V]]

    def row(self, s):
        from verifica_parametro import R, Surd, V, q as slope
        half = Q(1, 2)
        u = s - half
        if not (0 < s < half-self.eps or self.eps < u < R):
            return None
        if self.knots[-1] <= u <= V or any(abs(s-z) <= self.gamma for z in self.cusps):
            return None
        weight = max(Surd(0), Surd.lift(-u)) + max(Surd(0), Surd.lift(u)-V)
        delta = Surd(0)
        for lo, hi in zip(self.knots, self.knots[1:]):
            if lo < u < hi:
                weight = (u-lo)*(hi-u)
                delta = slope*(u-lo)
                break
        cusp = 8 * sum((abs(s-z) for z in self.cusps), Surd(0)) / self.gamma
        return weight, delta, cusp


def grid_for(q, m, b, features):
    from verifica_parametro import Cell
    from weights import weight_for_gap
    h = (max(1024, 1 << b)*m-1).bit_length()
    # The engine supplies the shared angular prefix tables. Its original row
    # descriptors are replaced with the plateau descriptors before extraction.
    grid = features.Grid(q, m, h)
    profile = Plateau(m)
    unit = grid.D
    perspective_scale = grid.K // (1 << b)
    assert perspective_scale * (1 << b) == grid.K
    for i in range(q):
        s = Q(i, q)
        row = profile.row(s)
        if row is None:
            grid.row[i] = (-1, 0, 0, [])
            continue
        weight, delta, cusp = row
        label = weight_for_gap(weight, h)
        base = (64*grid.K*i*i + 8*perspective_scale*i*q)*unit**2
        base += 64*q*q*unit*features.floor_surd(cusp*unit)
        perspective = 4*q*q*perspective_scale*features.floor_surd(weight*weight*unit)
        arcs = []
        sheets = ('L',) if s < Q(1, 2) else ('+', '-')
        for sheet in sheets:
            lo, hi = Cell(None, None, sheet).edges(s)
            if sheet == '-':
                lo += delta
            if sheet != 'L':
                hi += delta/2
            first = features.floor_surd((lo+profile.eps)*q)+1
            stop = -features.floor_surd((profile.eps-hi)*q)
            if first < stop:
                arcs.extend((l, r, sheet) for l, r in features.segments(first, stop-first, q))
        grid.row[i] = (label, base, perspective, arcs)
    all_rows = (grid.partial(i, 0, q) for i in range(q))
    grid.rowsums = tuple(features.sums(column) for column in zip(*all_rows))
    grid.total = tuple(column[-1] for column in grid.rowsums)
    return grid


def candidate(n, q, m, b, construct, features):
    from weights import certificate, ceil_sqrt, select_direction, unconditional_separation
    grid = grid_for(q, m, b, features)
    size, labelsum, *_ = grid.total
    if not size:
        return []
    lower = min(label for label, _, _, arcs in grid.row if arcs)
    ell = max(m*lower, m*labelsum//size - 8*(grid.h+2)*ceil_sqrt(m))
    cert = certificate(n, q, m, grid.h, ell)
    if cert is None:
        direction = [(1, 1)]*m
        u = unconditional_separation(direction, q, n, grid.H)
    else:
        u, primary, angular = cert
        direction = select_direction(n, m, q, primary, angular)
        u = max(u, unconditional_separation(direction, q, n, grid.H))
    if u <= 0:
        return []
    width = u / (1 << (2*b+10))
    if Q(8*m*grid.K, grid.D) > width:
        return []
    _, eligible = construct.translate(n, grid, direction)
    return construct.extract(eligible, width, grid.scale, ell)


def solve(n, engine_dir):
    if n < 1:
        raise ValueError('N must be positive')
    if n == 1:
        return dict(N=1, sites=[1])
    construct, features = import_engine(engine_dir)
    m, q = construct.choose_dimension(n), construct.first_prime(n)
    best = digit_witness(n)
    assert progression_free(n, best)
    chosen = None
    for b in range(1, n.bit_length().bit_length()+1):
        sites = candidate(n, q, m, b, construct, features)
        if len(sites) > len(best) and progression_free(n, sites):
            best, chosen = sites, b
    return dict(N=n, m=m, q=q, method='plateau' if chosen else 'radix-182', parameter=chosen, sites=best)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('N', type=int)
    parser.add_argument('engine_dir', help='directory of the weighted algorithm at commit 0fb8014')
    args = parser.parse_args()
    print(json.dumps(solve(args.N, args.engine_dir)))
