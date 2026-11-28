"""Finite checks for near progressions, using only the Python standard library."""
from collections import Counter, defaultdict
from cmath import exp, pi
from itertools import combinations, product
from math import gcd, lcm


def defect(x, y, z):
    return x + z - 2*y


def ordinary_free(points):
    return all(a+c != 2*b for a, b, c in combinations(sorted(points), 3))


def has_edge(a, b, c, s, t):
    for mid, left, right in ((a, b, c), (b, a, c), (c, a, b)):
        value = defect(left, mid, right)
        if value % t == 0 and abs(value) <= 2*s*t:
            return True
    return False


def free_subsets(n, edges):
    """Independence recursion adding each site only after all lower sites."""
    pairs = [[] for _ in range(n)]
    for a, b, c in edges:
        pairs[c].append((1 << a) | (1 << b))
    subsets = [0]
    for c in range(n):
        subsets.extend([mask | (1 << c) for mask in subsets
                        if all(mask & pair != pair for pair in pairs[c])])
    return subsets


def elements(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]


def ceiling(a, b):
    return (a+b-1)//b


def discrete_checks():
    n = 12
    triples = list(combinations(range(n), 3))
    ordinary = free_subsets(n, [p for p in triples if defect(*p) == 0])
    capacities = [max(len(elements(mask)) for mask in ordinary if mask < 1 << j)
                  for j in range(n+1)]
    robust_cases = thinning_cases = sheet_cases = 0
    for s in range(1, 6):
        digit = next(elements(mask) for mask in ordinary if mask < 1 << (s+1)
                     and len(elements(mask)) == capacities[s+1])
        for t in range(1, n+3):
            edges = [p for p in triples if has_edge(*p, s, t)]
            independent = free_subsets(n, edges)
            maxima = [0]*(n+1)
            for mask in independent:
                points = elements(mask)
                lists = defaultdict(list)
                for x in points:
                    lists[x % (t//gcd(2, t))].append(x)
                thin = [x for column in lists.values() for x in column[::2]]
                assert 2*len(thin) >= len(points)
                for x, y, z in product(thin, repeat=3):
                    v = defect(x, y, z)
                    if v % t == 0 and abs(v) <= 2*s*t:
                        assert x == y == z
                image = {x+t*u for x in thin for u in digit}
                assert len(image) == len(thin)*len(digit) and ordinary_free(image)
                projected = [a-t*((s-1)*a//(s*t)) for a in points]
                assert max(Counter(projected).values(), default=0) <= 2
                assert ordinary_free(set(projected))
                maxima[mask.bit_length()] = max(maxima[mask.bit_length()], len(points))
                thinning_cases += 1
            for m in range(1, n+1):
                maxima[m] = max(maxima[m], maxima[m-1])
                compressed = min(m, ceiling(m, s)+t)
                assert capacities[compressed] <= 6*maxima[m]
                assert maxima[m] <= 2*capacities[compressed]
                L = 2*s+2
                small = ceiling(m, L)
                for base in ordinary:
                    if base >= 1 << small:
                        continue
                    expanded = [b+t*((L-1)*b//t) for b in elements(base)]
                    assert len(set(expanded)) == len(expanded)
                    assert all(0 <= x < m for x in expanded)
                    assert all(not has_edge(*triple, s, t)
                               for triple in combinations(expanded, 3))
                robust_cases += 1
    for mask in ordinary:
        a = elements(mask)
        signed = Counter(defect(*v) for v in product(a, repeat=3))
        for t in range(-5, 6, 2):
            union = sorted({2*x for x in a} | {2*x+t for x in a})
            actual = 2*sum(x+z == 2*y for x, y, z in combinations(union, 3))
            assert actual == signed[t] + signed[-t]
            sheet_cases += 1
    return robust_cases, thinning_cases, sheet_cases


def signed_counts(weights):
    sums = Counter()
    for x, u in enumerate(weights):
        for z, v in enumerate(weights):
            sums[x+z] += u*v
    out = Counter()
    for k, mass in sums.items():
        for y, w in enumerate(weights):
            out[k-2*y] += mass*w
    return out


def grid_checks():
    windows = frequencies = 0
    for n in (13, 19, 29):
        points = [x for x in range(n) if (x*x+3*x+5) % 11 < 5]
        assert points
        for q, J in product((1, 2, 3, 4), (2, 3, 5, 9)):
            cells = defaultdict(list)
            for x in range(n):
                cells[(J*x//n, x % q)].append(x)
            den = lcm(*(len(c) for c in cells.values()))
            input_w = [den*int(x in points) for x in range(n)]
            avg = [0]*n
            for c in cells.values():
                mass = sum(input_w[x] for x in c)
                assert mass % len(c) == 0
                for x in c:
                    avg[x] = mass//len(c)
            M = sum(input_w)
            assert sum(avg) == M
            assert sum((n*y-M)**2 for y in avg) <= n*M*(n*max(avg)-M)
            before, after = signed_counts(input_w), signed_counts(avg)
            width = ceiling(n, J)
            for center, H, b in product((-n//2, 0, n//3), (3, n//2, n), range(q)):
                def band(counts, radius):
                    return sum(v for k, v in counts.items()
                               if abs(k-center) <= radius and k % q == b)
                assert band(after, H-4*width) <= band(before, H) <= band(after, H+4*width)
                windows += 1
            for shift in (0, 0.3/n, 1.2/n):
                errors = [sum((input_w[x]-avg[x])*exp(2j*pi*x*(r/q+shift))
                              for x in range(n)) for r in range(q)]
                left = sum(abs(v)**2 for v in errors)
                by_residue = [sum((input_w[x]-avg[x])*exp(2j*pi*x*shift)
                                  for x in range(r, n, q)) for r in range(q)]
                right = q*sum(abs(v)**2 for v in by_residue)
                assert abs(left-right) <= 1e-9*max(1, M*M)
                column_mass = [sum(input_w[r::q]) for r in range(q)]
                bound = q*(4*pi*width*abs(shift))**2*sum(v*v for v in column_mass)
                assert left <= bound + 1e-9*max(1, M*M)
                frequencies += 1
    return windows, frequencies


def larger_rounding_checks():
    expanded_cases = uniform_cases = 0
    for s, t in product((1, 2, 3, 7, 13), (1, 2, 3, 6, 23, 68)):
        L = 2*s+2
        image = [b+t*((L-1)*b//t) for b in range(24)]
        for a, b, c in combinations(range(len(image)), 3):
            if a+c != 2*b:
                assert not has_edge(image[a], image[b], image[c], s, t)
                expanded_cases += 1
    for n in (8, 17, 31, 48):
        counts = signed_counts([1]*n)
        for q in (1, 2, 3, 5, 9):
            for H, b in product(range(1, n+1), range(q)):
                total = sum(v for k, v in counts.items() if abs(k) <= H and k % q == b)
                # Uniform residue discrepancy <= 1/n. Moving the three
                # uniform points to integer sites moves the defect by <= 4/n.
                assert abs(6*q*total - (6*n*n*H-H**3)) <= 6*(q+4)*n*n
                uniform_cases += 1
    return expanded_cases, uniform_cases


if __name__ == "__main__":
    robust, thinning, sheets = discrete_checks()
    windows, frequencies = grid_checks()
    expanded, uniform = larger_rounding_checks()
    print("Finite (n,s,t) capacity checks:", robust)
    print("Independent-set thinning and digit expansions:", thinning)
    print("Ordered two-copy identities:", sheets)
    print("Exact rational transport windows:", windows)
    print("Finite Fourier orthogonality checks (floating point):", frequencies)
    print("Nonprogression triples tested under the expanding map:", expanded)
    print("Uniform residue windows checked against the cubic integral:", uniform)
