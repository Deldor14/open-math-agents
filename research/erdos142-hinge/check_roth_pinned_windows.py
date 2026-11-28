"""Finite integer checks for sparse repair, aligned tests, and mandatory AP-free sites."""
from itertools import combinations


def windows(n, length):
    if length == 1:
        return [1 << x for x in range(n)]
    return [sum(1 << (start+j*step) for j in range(length))
            for step in range(1, (n-1)//(length-1)+1)
            for start in range(n-(length-1)*step)]


def families(n):
    triples = windows(n, 3)
    return [s for s in range(1 << n) if all(s & t != t for t in triples)]


def weights_audit(n):
    family = families(n)
    triples = windows(n, 3)
    cases = 0
    for excluded in [0]+[(1 << j)-1 for j in range(1,n)]+[sum(1 << i for i in range(0,n,2))]:
        weight = {a: 3**(n-bin(a).count("1")) for a in family if not a & excluded}
        total = sum(weight.values())
        for v in range(n):
            flag = 1 << v
            if excluded & flag:
                continue
            links = [t ^ flag for t in triples if t & flag]
            present = sum(w for a,w in weight.items() if a & flag)
            eligible = sum(w for a,w in weight.items() if (a | flag) in weight)
            assert 4*present == eligible <= total
            pairs = [sum(w for a,w in weight.items() if (a & link) == link) for link in links]
            assert all(16*z <= total for z in pairs)
            assert 4*present >= total-sum(pairs)
            cases += 1
    return cases


def exact_thresholds(n):
    family = families(n)
    thresholds = []
    for length in range(2,n+1):
        target = windows(n,length)
        extensible = bytearray(1 << n)
        for mask in family:
            if all(mask & w for w in target):
                extensible[mask] = 1
        # Every subset of an admissible complete extension is recorded.
        for mask in reversed(range(1 << n)):
            if extensible[mask]:
                bits = mask
                while bits:
                    bit = bits & -bits
                    extensible[mask ^ bit] = 1
                    bits ^= bit
        thresholds.append(min((bin(s).count("1")-1 for s in family if not extensible[s]),default=n))
        if n <= 9:
            direct = [a for a in family if all(a & w for w in target)]
            assert all(bool(extensible[s]) == any((s & a)==s for a in direct) for s in family)
    return thresholds


def digital_examples():
    digits = {0}
    for m in range(8):
        period = 4**m
        a = (period-1)//3
        forced = {a-x for x in digits} | {2*a+1+y for y in digits}
        assert len(forced) == 2*2**m and min(forced) == 0 and max(forced) == period
        forbidden = set()
        for x,y in combinations(sorted(forced),2):
            forbidden.update((2*y-x,2*x-y))
            if (x+y)%2 == 0:
                forbidden.add((x+y)//2)
        assert forbidden.isdisjoint(forced)
        assert all(x in forbidden for x in range(period+1,2*period+1))
        digits = {4*x+bit for x in digits for bit in (0,1)}
    return period, len(forced)


def aligned_examples():
    tested = 0
    for n in range(3,75):
        for length in range(2,n+1):
            stride = max(1,length//5)
            h = length-stride
            for q in range(1,(n-1)//(length-1)+1):
                for a in range(n-(length-1)*q):
                    j = (- (a//q)) % stride
                    start = a+j*q
                    assert j+h<=length and (start//q)%stride==0
                    assert start+(h-1)*q<n
                    tested += 1
    return tested


if __name__ == '__main__':
    print('exact occupation checks:', weights_audit(12))
    print('aligned positive-step windows:', aligned_examples())
    for n in (8,9,13,16):
        print('n, exact maximum prescription sizes for L=2,...,n:',n,exact_thresholds(n))
    print('largest digital example, forced interval and seed size:',digital_examples())
