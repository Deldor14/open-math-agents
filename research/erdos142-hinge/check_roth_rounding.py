"""Exact finite regressions for periodic rounding and dyadic rigidity."""
from fractions import Fraction
from itertools import combinations
from math import ceil, gcd, isqrt


def midpoint_rank(points, period):
    """Row reduction over F_257. Full rank modulo 257 certifies real rank."""
    modulus = 257
    pos = {x: i for i, x in enumerate(points)}
    rows = {}
    for y in points:
        for x in points:
            z = (2*y-x) % period
            if x > z or x == y or z not in pos:
                continue
            row = [0]*len(pos)
            row[pos[x]] += 1
            row[pos[z]] += 1
            row[pos[y]] -= 2
            for j in range(len(row)):
                factor = row[j] % modulus
                if not factor:
                    continue
                if j not in rows:
                    inverse = pow(factor, -1, modulus)
                    rows[j] = [(a*inverse) % modulus for a in row]
                    break
                row = [(a-factor*b) % modulus for a, b in zip(row, rows[j])]
    return len(rows)


def check_rigidity():
    cases = represented = 0
    for period in (1, 2, 4, 8, 16):
        size = period//2+1
        seen = set()
        for points in combinations(range(period), size):
            if points in seen:
                continue
            orbit = {tuple(sorted((a+x) % period for a in points)) for x in range(period)}
            seen.update(orbit)
            assert midpoint_rank(points, period) == size-1
            cases += 1
        represented += len(seen)
    return cases, represented


def capacities(limit):
    free = [0]
    values = [0]
    for x in range(limit):
        masks = [(1 << (x-d)) | (1 << (x-2*d)) for d in range(1, x//2+1)]
        free.extend([b | (1 << x) for b in free if all(b & m != m for m in masks)])
        values.append(max(bin(v).count('1') for v in free))
    return values


def check_transfer():
    R = capacities(22)
    inequalities = triples = periods = 0
    for p in range(1, 26):
        for q in range(1, p+1):
            if gcd(p, q) != 1 or p > 4*q:
                continue
            copies = (p+1)//2
            for n in range(1, len(R)):
                length = ceil(Fraction(p*(2*n-1), 2*q))
                if length < len(R):
                    assert R[length] >= ceil(Fraction(copies*R[n], q))
                    inequalities += 1
            for b in (-3, 0, 2):
                points = {y: (q*y+b)//p for y in range(-p, 3*p) if 2*((q*y+b)%p)<p}
                assert sum(0<=y<p for y in points) == copies
                for y in points:
                    for x in points:
                        z = 2*y-x
                        if x<y and z in points:
                            assert points[x] < points[y] < points[z]
                            assert points[x]+points[z] == 2*points[y]
                            triples += 1
                periods += 1
    return periods, triples, inequalities


def curved_checks():
    output_progressions = separated = 0
    for n, error in ((83, 2), (153, 4), (292, 2), (346, 7)):
        width = isqrt(n*error//2)
        blocks = n//(2*width)
        best = ()
        for size in range(1, blocks+1):
            witness = next((t for t in combinations(range(blocks), size)
                            if all(a+c != 2*b for a, b, c in combinations(t, 3))), None)
            if witness is None:
                break
            best = witness
        labels = {}
        for u in best:
            a = 2*width*u
            choices = []
            for half_shift in (0, 1):
                row = {}
                for y in range(a, a+width):
                    # 2n times the tangent to y+y^2/n plus the shift.
                    num = 2*n*y+4*a*y-2*a*a+half_shift*n
                    if num % (2*n) < n:
                        row[y] = num//(2*n)
                choices.append(row)
            chosen = max(choices, key=len)
            assert 2*len(chosen) >= width
            labels.update(chosen)
        assert all(abs(n*value-(n*y+y*y)) <= n*error for y, value in labels.items())
        for x in labels:
            for y in labels:
                z = 2*y-x
                if x < y and z in labels:
                    assert labels[x] < labels[y] < labels[z]
                    assert labels[x]+labels[z] == 2*labels[y]
                    output_progressions += 1
        # Upper obstruction, independently allowing the worst errors at all
        # three sites. Choose the first integer d with 2*d^2 >= 9*n*error.
        step = max(3*error, isqrt((9*n*error-1)//2)+1)
        for d in range(step, (n-1)//2+1):
            for y in range(d, n-d):
                x, z = y-d, y+d
                a, b, c = (n*j+j*j for j in (x, y, z))
                assert a+n*error < b-n*error and b+n*error < c-n*error
                assert a+c-2*n*error > 2*(b+n*error)
                separated += 1
    return output_progressions, separated


if __name__ == '__main__':
    orbits, sets = check_rigidity()
    periods, triples, inequalities = check_transfer()
    inside, outside = curved_checks()
    print("Dyadic majority supports represented:", sets)
    print("Exact modular rank certificates after translation:", orbits)
    print("Rational masks and shifts checked:", periods)
    print("Progressions checked in the masks:", triples)
    print("Finite Roth-number inequalities checked:", inequalities)
    print("Output progressions in explicit quadratic tubes:", inside)
    print("Quadratic progressions tested at worst-case error:", outside)
