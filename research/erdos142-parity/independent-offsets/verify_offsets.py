"""Exact offset probabilities and an exhaustive small-set check of the matching argument."""
from collections import Counter
from itertools import combinations, permutations, product


def charge(i, j, k):
    return i + k - 2*j


def free(points):
    sites = set(points)
    return all(2*y-x not in sites for x, y in combinations(sorted(sites), 2))


def check_probabilities():
    for counts in ((1, 1, 1), (5, 2, 5), (2, 3, 7)):
        a, b, c = counts
        actual = Counter()
        for i, j, k in product(range(3), repeat=3):
            actual[charge(i, j, k)] += counts[i]*counts[j]*counts[k]
        assert actual[-4] == a*a*c and actual[4] == c*c*a
        assert actual[-1] == 2*a*b*b+2*b*c*c
        assert actual[1] == 2*c*b*b+2*b*a*a
        assert actual[-2] == a*a*b+2*a*c*c+b*b*c
        assert actual[2] == c*c*b+2*c*a*a+b*b*a
    assert {charge(*idx) for idx in permutations(range(3))} == {-3, 0, 3}


def check_outputs():
    # Cover all extremizers on nine sites, all displacement-one offset
    # assignments, and every progression-free subset of each distinct image.
    candidates = [u for k in range(10) for u in combinations(range(9), k) if free(u)]
    M = max(map(len, candidates))
    optimizers = [u for u in candidates if len(u) == M]
    image_info = {}
    checked = 0
    for A in optimizers:
        used, matching = set(), []
        for triple in permutations(range(M), 3):
            x, y, z = (A[i] for i in triple)
            if abs(charge(x,y,z)) in (1,2,4) and used.isdisjoint(triple):
                used.update(triple)
                matching.append(triple)
        assert matching
        for offsets in product(range(3), repeat=M):
            points = tuple(x+d for x,d in zip(A, offsets))
            image = tuple(sorted(set(points)))
            successes = 0
            for i, j, k in matching:
                if charge(points[i], points[j], points[k]) == 0:
                    assert len({points[i], points[j], points[k]}) == 3
                    successes += 1
            if image not in image_info:
                image_info[image] = max(k for k in range(len(image)+1)
                                         if any(free(Y) for Y in combinations(image,k)))
            alpha = image_info[image]
            assert M-alpha >= successes and 3*(len(image)-alpha) >= successes
            checked += 1
    print("Extremizers on nine sites:", len(optimizers), "offset assignments:", checked)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must be enabled.")
    check_probabilities()
    check_outputs()
