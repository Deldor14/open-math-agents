"""Integer check of weighted retention and positive-step hitting after gluing two sets."""
from random import Random


def greedy(points, seed):
    order = sorted(points)
    Random(seed).shuffle(order)
    chosen = set()
    forbidden = set()
    for x in order:
        if x in forbidden:
            continue
        for y in chosen:
            forbidden.update((2*x-y, 2*y-x))
            if (x+y) % 2 == 0:
                forbidden.add((x+y)//2)
        chosen.add(x)
    return chosen


def assert_free(points):
    assert all(2*y-x not in points for x in points for y in points if x < y)


def longest_empty(n, points):
    longest = 0
    for q in range(1, n):
        if 1 + (n-1)//q <= longest:
            break
        for a in range(q):
            run = 0
            for x in range(a, n, q):
                run = 0 if x in points else run+1
                longest = max(longest, run)
    return longest


def windows(n, length):
    for q in range(1, (n-1)//(length-1)+1):
        for a in range(n-(length-1)*q):
            yield a, q


def check():
    n, p = 4007, 5
    seed = greedy(range(2*n//3, n), 142)
    blocker = greedy(range(n), 142)
    ell = longest_empty(n, blocker)+1
    # A full p-period for every index of the short progression.
    length = max(p*ell, (n-1)//p+2)
    assert (n-1)//(length-1) == p-1
    assert longest_empty(n, seed) >= length
    assert_free(seed)
    assert_free(blocker)
    weights = {x: 1+(x*x+3*x) % 17 for x in seed}
    retained = []
    tested = 0
    for phase in range(p):
        reserve = {x for x in seed if (x+phase) % p == 0}
        aux = {x for x in blocker if (x+phase) % p == 1}
        glued = reserve | aux
        assert_free(glued)
        retained.append(sum(weights[x] for x in reserve))
        for a,q in windows(n, length):
            b = ((1-a-phase)*pow(q,-1,p)) % p
            assert b+(ell-1)*p < length
            short = range(a+b*q, a+(b+ell*p)*q, p*q)
            assert all(0 <= x < n and (x+phase) % p == 1 for x in short)
            assert not aux.isdisjoint(short)
            tested += 1
        assert longest_empty(n, glued) < length
    assert sum(retained) == sum(weights.values())
    assert p*max(retained) >= sum(weights.values())
    print(f'n={n}, seed={len(seed)}, blocker={len(blocker)}, ell={ell}, L={length}')
    print(f'all {tested} window/phase pairs, positive steps 1 through {p-1}')
    print(f'weighted overlaps={retained}, total seed weight={sum(weights.values())}')


if __name__ == '__main__':
    check()
