"""Independent meet-in-the-middle enumeration using only direct 3-AP tests."""
from collections import defaultdict
from functools import lru_cache

def has_triple(mask, length):
    return any(mask & (mask >> step) & (mask >> (2*step))
               for step in range(1, (length+1)//2))

@lru_cache(maxsize=None)
def half_sets(length):
    by_size = defaultdict(list)
    for mask in range(1 << length):
        if not has_triple(mask, length):
            by_size[bin(mask).count("1")].append(mask)
    return by_size

def extremizers(n, size):
    m = n//2
    left, right = half_sets(m), half_sets(n-m)
    for k, masks in left.items():
        for a in masks:
            for b in right.get(size-k, ()):
                candidate = a | (b << m)
                if not has_triple(candidate, n):
                    yield candidate

if __name__ == "__main__":
    for n, target in [(31,12),(32,13),(33,13),(35,13),(36,14),(37,14)]:
        assert next(extremizers(n,target+1), None) is None
        core = (1 << n)-1
        count = 0
        for mask in extremizers(n,target):
            core &= mask
            count += 1
        sites = [i + 1 for i in range(n) if core & (1 << i)]
        if n in (33, 37):
            assert count == 4 and sites == [2, n - 1]
        assert count
        print(n, target, count, sites, flush=True)
