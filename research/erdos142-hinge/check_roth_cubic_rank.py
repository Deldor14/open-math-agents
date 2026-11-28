"""Exact negative dependence, sharp penalties, and full finite rounding tests."""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import random


def penalty(k):
    return F(k**k, (k-1)**(k-1))-k


def choices(weights, edge):
    """Leave coordinates above level t fixed and omit one other coordinate."""
    k = len(edge)
    small = sorted(edge, key=lambda i: weights[i])
    while len(small) >= 2:
        t = sum((weights[i] for i in small), F(0))/(len(small)-1)
        if weights[small[-1]] <= t:
            break
        small.pop()
    assert len(small) >= 2
    result = []
    for missing in small:
        p = 1-weights[missing]/t
        if p:
            w = list(weights)
            for i in small:
                w[i] = t if i != missing else F(0)
            result.append((p,w))
    assert sum(p for p,_ in result)==1
    return result


def check_local(w):
    k = len(w)
    rows = choices(w, range(k))
    for _,r in rows:
        assert sum(r)==sum(w) and min(r)==0
    for size in range(1,k):
        for s in combinations(range(k),size):
            before = prod(w[i] for i in s)
            after = sum(p*prod(r[i] for i in s) for p,r in rows)
            assert (after==before if size==1 else after<=before)
    old = sum(x**k for x in w)+penalty(k)*prod(w)
    assert sum(p*sum(x**k for x in r) for p,r in rows)<=old


def cost(w,edges,k):
    return sum(x**k for x in w)+penalty(k)*sum(prod(w[i] for i in e) for e in edges)


def round_free(w,edges,k):
    initial = cost(w,edges,k)
    total = sum(w)
    while True:
        edge = next((e for e in edges if all(w[i] for i in e)), None)
        if edge is None:
            size = sum(x>0 for x in w)
            assert sum(w)==total and initial*size**(k-1)>=total**k
            return size
        rows = choices(w,edge)
        before = cost(w,edges,k)
        after,w = min((cost(u,edges,k),u) for _,u in rows)
        assert after<=before


def exact_rank(n,edges):
    masks = [sum(1<<i for i in e) for e in edges]
    return max(bin(s).count('1') for s in range(1<<n)
               if all(s&e != e for e in masks))


def main():
    local = 0
    for k in range(2,9):
        # One representative from each permutation orbit.
        from itertools import combinations_with_replacement
        for w in combinations_with_replacement(range(1,6),k):
            check_local(tuple(map(F,w)))
            local += 1
        u = [F(1)]*k
        assert sum(x**k for x in u)+penalty(k)*prod(u)==F(k**k,(k-1)**(k-1))
    rng = random.Random(142)
    checked = 0
    triples = list(combinations(range(5),3))
    for mask in range(1<<len(triples)):
        e = [t for i,t in enumerate(triples) if mask>>i&1]
        w = [F(rng.randrange(1,10)) for _ in range(5)]
        s = round_free(w,e,3)
        r = exact_rank(5,e)
        assert s<=r and sum(w)**3<=r*r*cost(w,e,3)
        checked += 1
    other = 0
    for k in range(2,8):
        for _ in range(25):
            n = k+3
            edges = [e for e in combinations(range(n), k) if rng.random()<0.21]
            w = [F(rng.randrange(1,8)) for _ in range(n)]
            s = round_free(w,edges,k)
            assert s<=exact_rank(n,edges)
            other += 1
    print('Local rational tuples:',local)
    print('All labelled triple systems on five vertices:',checked)
    print('Additional uniform hypergraphs:',other)


if __name__ == '__main__':
    main()
