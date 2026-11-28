"""Check a primary-grid width certificate using Python integer arithmetic only."""
import gzip
from fractions import Fraction
from pathlib import Path
import json
import sys


def triples(n, mask):
    def occupied(i):
        return bool(mask & (1 << i))
    return [(x, z, (x+z+n)//2) for x in range(n) for z in range(x, n-x)
            if (x+z+n)%2 == 0 and all(occupied(k) for k in (x,z,(x+z+n)//2))]


def known_row(t, groups):
    ranks = {index: i for i, group in enumerate(groups) for index in group}
    # A midpoint's character acts on twice the row coordinate.
    exponents = [ranks[k] - (i == 2) if k in ranks else None for i,k in enumerate(t)]
    highest = max((h for h in exponents if h is not None), default=0)
    return [2**(highest-h) if h is not None else 1 for h in exponents]


def children(groups, x):
    for j in range(len(groups)):
        yield [g+[x] if k == j else g for k,g in enumerate(groups)]
    for j in range(len(groups)+1):
        yield groups[:j]+[[x]]+groups[j:]


def active_indices(n, mask):
    return [x for x in range(n) if mask & (1 << x)]


def rank_order(indices, rows):
    return sorted(indices, key=lambda x: -sum(t.count(x) for t in rows))


def dual_check(dual, n, target, active, rows, rankings):
    d, terms = dual
    assert type(d) is int and d > 0
    load = [0]*n
    cost = 0
    for ri, numerator in terms:
        assert type(ri) is int and 0 <= ri < len(rows)
        assert type(numerator) is int and numerator > 0
        row = rows[ri]
        possible = [known_row(row,g) for g in rankings]
        # Each partial ranking bounds each actual coefficient from below.
        for k, v in zip(row, map(max,zip(*possible))):
            load[k] += numerator*v
        cost += numerator
    double_cost = 2*cost + sum(max(0,d-load[k]) for k in active)
    assert double_cost*target.denominator <= 2*d*n*target.numerator


def merges(a,b):
    """All total orders with ties extending the two disjoint ordered partitions."""
    if not a or not b:
        yield a+b
        return
    for lead, rest in ((a[0],(a[1:],b)), (b[0],(a,b[1:])), (a[0]+b[0],(a[1:],b[1:]))):
        for tail in merges(*rest):
            yield [lead]+tail


def check(path, target, allow_survivors=False):
    with gzip.open(path, 'rt') as f:
        proof = json.load(f)
    n = proof['grid']
    assert n == 12 and target == Fraction(proof['cap'])
    survivors = []
    leaf = proof['duals']
    data = iter(proof['nodes'])
    pruned = 0
    splits = 0
    max_depth = 0

    def visit(groups, depth):
        nonlocal pruned, splits, max_depth
        max_depth = max(max_depth,depth)
        code = next(data)
        if code == -2:
            assert allow_survivors and depth == len(order)
            survivors.append(groups)
            return
        if code == -1:
            assert depth < len(order)
            splits += 1
            for g in children(groups, order[depth]):
                visit(g,depth+1)
            return
        assert type(code) is int and 0 <= code < len(leaf)
        dual_check(leaf[code], n, target, active, rows, [groups])
        pruned += 1

    for mask in range(1<<n):
        active = active_indices(n, mask)
        if Fraction(len(active),2) <= n*target:
            continue
        rows = triples(n, mask)
        order = rank_order(active,rows)
        visit([],0)
    assert list(data) == []
    print(f"Grid {n}, upper mean {target}, {pruned} checked duals in the tree, "
          f"{splits} splits, {len(leaf)} distinct duals, depth {max_depth}.")
    witness = proof.get('witness')
    if witness:
        widths = [Fraction(x) for x in witness['widths']]
        levels = witness['levels']
        assert len(widths)==len(levels)==n and all(0<=w<=Fraction(1,2) for w in widths)
        assert all(isinstance(v,int) and v>=0 for v in levels)
        mask=sum(1<<i for i,v in enumerate(widths) if v>0)
        for i,j,k in triples(n,mask):
            h=max(levels[i],levels[j],levels[k]-1)
            assert (2**(h-levels[i])*widths[i]+2**(h-levels[j])*widths[j]
                    +2**(h-levels[k]+1)*widths[k])<=1
        assert sum(widths)==n*target
        print("The finite width relaxation has a matching rational witness.")


    return survivors


def pair_check(path, survivors):
    with gzip.open(path,'rt') as f:
        proof=json.load(f)
    data=iter(proof['nodes'])
    regular=refined=complete=0
    for a0 in survivors:
        for b0 in survivors:
            a=[[2*x for x in g] for g in a0]
            b=[[2*x+1 for x in g] for g in b0]
            active=sorted(x for g in a+b for x in g)
            rows=triples(24,sum(1<<x for x in active))
            def consume(code,rankings):
                assert type(code) is int and 0<=code<len(proof['duals'])
                dual_check(proof['duals'][code],24,Fraction(3,10),active,rows,rankings)
            code=next(data)
            if code==-1:
                refined+=1
                for g in merges(a,b):
                    consume(next(data),[g]);complete+=1
            else:
                consume(code,[a,b]);regular+=1
    assert list(data)==[]
    print(f"Paired grid: {regular} direct pairs, {refined} refined pairs, "
          f"{complete} interleavings. Upper mean 3/10.")


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    root=Path(__file__).resolve().parent
    assert not check(root/'bohr12.json.gz',Fraction(29,96))
    survivors=check(root/'near_certificate.json.gz',Fraction(143,480),True)
    assert len(survivors)==18
    pair_check(root/'paired_certificate.json.gz',survivors)
