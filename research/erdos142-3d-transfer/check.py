"""Check transfer kernels, phase moments and the actual 3D height on prime grids."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from random import Random
from sys import argv
from block import Block
from transfer import (add_phase,choose_axis,grid_data,min_metric,pick_shift,
                      residue,translate,window)


def kernel_checks():
    rng = Random(142)
    primes = [5,7,11]
    for t in range(100):
        weights = [rng.randrange(1,100) for _ in range(19+t%17)]
        a,scale = F(5+t,1+t%4),127
        (p,h),new = choose_axis(weights,primes,scale,a)
        def brute(q,r):
            total=0
            for d,w in enumerate(weights,1):
                j=d*r%q
                kernel=scale/(1+a*F(min(j,q-j)**2,q*q))
                total+=w*(-((-kernel.numerator)//kernel.denominator))
            return total
        assert sum(new)==brute(p,h)==min(brute(p,r) for r in range(p))
        assert sum(weights[p-1::p])==min(sum(weights[q-1::q]) for q in primes)
    return 100


def moment_checks():
    rng = Random(31)
    axes = [(3,1),(5,3),(3,2)]
    p = tuple(q for q,r in axes)
    count=0
    for trial in range(6):
        weights = {i:F(rng.randrange(-3,4),7) for i in range(1,90)}
        data = grid_data(axes,lambda z,s,t: None if (z+s+t)%1<F(1,3) else z*z+2*s+t)
        _,table,_=data
        constant=F(trial+7,5)
        def direct(h):
            values = [(u,table.get(add_phase(residue(i,axes),h,p))) for i,u in weights.items()]
            return sum(constant-(u+v)**2 for u,v in values if v is not None)
        h,survivors = pick_shift(weights,axes,data,constant)
        scores = [direct(k) for k in product(*(range(q) for q in p))]
        assert sum(constant-u*u for u in survivors.values())==max(scores)==direct(h)
        count+=len(scores)
    return count


def defect_grid(block,q,full):
    T=32*max(4*block.k,2*block.n)
    coords = range(q)
    entries={}
    for loc in product(coords,repeat=3):
        value = block.energy(*(F(i,q) for i in loc),T)
        if value is not None:
            entries[loc] = value
    metric_axis = [[F(weight*min(j,q-j)**2,q*q) for j in range(q)] for weight in (T*T,T,1)]
    def norm(u,v):
        return sum(metric_axis[i][((u[i]-v[i])*(1 if i==0 else 2))%q] for i in range(3))
    inv = pow(2,-1,q)
    if full:
        pairs=product(entries,repeat=2)
    else:
        rng=Random(99); pts=list(entries)
        pairs=((rng.choice(pts),rng.choice(pts)) for _ in range(100000))
    checked=0
    for u,v in pairs:
        if u==v:
            continue
        mid=tuple(((a+b)*inv)%q for a,b in zip(u,v))
        if mid in entries:
            assert norm(u,v)<=8*(entries[u]+entries[v]-2*entries[mid])
            checked+=1
    assert checked>0
    return len(entries),checked


def finite_window(block):
    T=32*max(4*block.k,2*block.n)
    N=23
    axes=[[(5,1),(7,2),(5,3)],[(7,3),(5,1),(7,4)]]
    alive,shifts,limit=translate(N,axes,lambda z,s,t:block.energy(z,s,t,T))
    sq=min_metric(N,axes,T)
    assert sq>0
    result=window(alive,sq)
    # Independent AP check and independent reconstruction from the selected shifts.
    for i,x in enumerate(result):
        for z in result[i+1:]:
            assert (x+z)%2 or (x+z)//2 not in result
    expected=[]
    for i in range(1,N+1):
        ok=True
        for vector,h in zip(axes,shifts):
            mod=tuple(p for p,v in vector)
            phase=add_phase(residue(i,vector),h,mod)
            ok &= block.energy(*(F(j,p) for j,p in zip(phase,mod)),T) is not None
        if ok:expected.append(i)
    assert list(alive)==expected
    return len(alive),result,shifts

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('checks require Python assertions')
    print('kernel instances',kernel_checks(),'all-shift score comparisons',moment_checks(),flush=True)
    b=Block(Path(argv[1])); assert b.volume==F(17063783,100663296)
    for p in (11,17,31):
        print('grid',p,'sites and nontrivial ordered AP tests',defect_grid(b,p,p<30),flush=True)
    print('small-grid concrete orbit',finite_window(b))
