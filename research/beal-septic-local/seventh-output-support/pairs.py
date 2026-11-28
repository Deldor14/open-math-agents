"""Count the two-base support obstruction by incidence and inclusion-exclusion."""
from collections import Counter, defaultdict
from itertools import combinations
from math import comb, prod
from support import bound, excluded, factors_of_order, primes

rationals = [r for r in primes if r <= bound]
factors = [factors_of_order(r) for r in rationals]
for use_descents in (False, True):
    sets = [s - excluded if use_descents else s for s in factors]
    counts = Counter()
    for s in sets:
        for k in range(len(s) + 1):
            for chosen in combinations(s, k):
                counts[prod(chosen), k] += 1
    disjoint = sum((-1)**k * comb(count, 2) for (_, k), count in counts.items())
    incidence = defaultdict(int)
    for i, s in enumerate(sets):
        for p in s:
            incidence[p] |= 1 << i
    shared = 0
    for i, s in enumerate(sets):
        row = 0
        for p in s:
            row |= incidence[p]
        shared += bin(row >> (i + 1)).count("1")
    total = comb(len(sets), 2)
    assert total == disjoint + shared
    print("with signed descents" if use_descents else "support criterion alone",
          "excluded", disjoint, "of", total, "pairs;", shared, "remain")
