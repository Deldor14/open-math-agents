"""Small exact checks for progression counts and the prime-cover inequality."""
from collections import Counter
from itertools import combinations


def popcount(mask):
    return bin(mask).count("1")


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def progressions(n, k):
    return [sum(1 << (a + i*d) for i in range(k))
            for d in range(1, (n - 1)//(k - 1) + 1)
            for a in range(n - (k - 1)*d)]


def direct_free(mask, k, n):
    for d in range(1, (n - 1)//(k - 1) + 1):
        starts = mask
        for i in range(1, k):
            starts &= mask >> (i*d)
        if starts:
            return False
    return True


def census(n, k):
    # Generate free sets recursively, testing only progressions ending at the new point.
    edges = progressions(n, k)
    sets = [0]
    capacities = [0]
    for i in range(n):
        bit = 1 << i
        endings = [e ^ bit for e in edges if e.bit_length() == i + 1]
        extra = [mask | bit for mask in sets if all(mask & part != part for part in endings)]
        sets.extend(extra)
        capacities.append(max(map(popcount, sets)))
    direct = [mask for mask in range(1 << n) if direct_free(mask, k, n)]
    assert set(sets) == set(direct)
    assert len(sets) >= 2**capacities[-1]
    return capacities, len(sets)


def cover_families(contained, k):
    full_edges = set(contained)
    first_pairs, mixed = set(), set()
    for i, edge in enumerate(contained):
        points = list(bits(edge))
        first_pairs.add((1 << points[0]) | (1 << points[1]))
        width = 2 + i % (k - 1)
        mixed.add(sum(1 << v for v in points[-width:]))
    return (full_edges, first_pairs, mixed)


def run(n=12):
    primes = (2, 3, 5, 7)
    checks = 0
    strict_excess = 0
    for k in (3, 4, 5):
        capacity, total = census(n, k)
        edges = progressions(n, k)
        print("n={}, k={}, r={}, I={}".format(n, k, capacity[n], total))
        for mask in range(1 << n):
            contained = [e for e in edges if mask & e == e]
            for cover in cover_families(contained, k):
                assert all(any(e & f == f for f in cover) for e in contained)
                # Track actual incidence and compare to divisibility of one fixed pair.
                pairs = {f: tuple(bits(f))[:2] for f in cover}
                multiplicities = Counter()
                deficits = 0
                for p in primes:
                    residue_hits = 0
                    for f, (x, y) in pairs.items():
                        if (y - x) % p == 0:
                            multiplicities[f] += 1
                            residue_hits += all((z - x) % p == 0 for z in bits(f))
                    lo, extra = divmod(n, p)
                    sum_capacity = (p - extra) * capacity[lo] + extra * capacity[lo + 1]
                    # Sharpen the ceiling bound by using the actual residue class sizes.
                    deficit = max(0, popcount(mask) - sum_capacity)
                    assert deficit <= residue_hits
                    deficits += deficit
                assert deficits <= sum(multiplicities.values()) <= (n.bit_length()-1) * len(cover)
                checks += 1
                strict_excess += deficits > 0
    assert strict_excess
    print("{} covers checked, {} with positive summed deficit".format(checks, strict_excess))


if __name__ == "__main__":
    run()
