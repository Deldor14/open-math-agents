"""Independent direct checks for the rational cell laws, extraction and geometry."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from random import Random
import sys
from extract import (ZERO, add, alphabet, clean, colour_counts, extract, fast_product,
                     haar, passes, phase, phase_cells, residual_laws)


def atoms():
    checked = 0
    for m in range(2,10):
        law = Counter()
        for t,k in phase_cells(m):
            law[t] += k
        assert sum(law.values()) == 4*m*m
        for p in (11,17,29,43,53):
            counts = Counter((m*x//p,m*y//p,m*((2*y-x)%p)//p)
                             for x in range(p) for y in range(p))
            assert counts.keys() <= law.keys()
            for t,w in law.items():
                assert abs(Q(counts[t],p*p)-Q(w,4*m*m)) <= Q(12,m*p)+Q(12,p*p)
                checked += 1
    for m in (2,3,5):
        law = Counter()
        for t,w in phase_cells(m):
            law[t] += w
        choices = list(alphabet(11))
        for i in (1,4):
            for gap in (1,11,13,17,19,22,143,11*13*17):
                ct = Counter(tuple(phase(opt,i+gap*j,m) for j in range(3)) for opt in choices)
                assert ct.keys() <= law.keys()
                for t in law:
                    expected = 0
                    for p in {opt[0] for opt in choices}:
                        if gap%p:
                            expected += sum((m*x//p,m*y//p,m*((2*y-x)%p)//p) == t
                                            for x in range(p) for y in range(p))
                        elif t[0] == t[1] == t[2]:
                            expected += p*sum(m*x//p == t[0] for x in range(p))
                    assert ct[t] == expected
                    checked += 1
    print(checked,'scalar grid atom comparisons including gaps divisible by several primes')

def coloured():
    rng = Random(142)
    for bits in (8191,8192,8193,20000,55000,90000):
        for _ in range(3):
            x,y = rng.getrandbits(bits),rng.getrandbits(bits)
            assert fast_product(x,y) == x*y
    colours = [None,ZERO,(1,4,True),(-2,7,False)]
    count = 0
    for seq in product(colours,repeat=6):
        one,three = colour_counts(seq)
        assert one == Counter((v,) for v in seq if v is not None)
        direct = Counter()
        for i,y in enumerate(seq):
            for j,x in enumerate(seq):
                k = 2*i-j
                if k != j and 0 <= k < len(seq) and None not in (x,y,seq[k]):
                    direct[x,y,seq[k]] += 1
        assert direct == three
        count += 1
    for mask in range(1<<10):
        s = [i+1 for i in range(10) if mask>>i&1]
        mids = {b for b in s for a in s if a<b and 2*b-a in s}
        assert clean(s) == [b for b in s if b not in mids]
    print(count,'coloured strings, 1024 midpoint deletions and 18 fast integer products')

def tiny():
    mesh = 2
    labels = {ij:(i-j,2*i+j,i==j==0) if (i,j)!=(1,1) else None
              for ij in product(range(2),repeat=2) for i,j in (ij,)}
    ones,three = haar(labels,mesh)
    for law,arity in ((ones,1),(three,3)):
        levels = residual_laws(law,2,arity)
        den = law[1]
        for param in ((-2,1,0),(0,2,2)):
            direct = sum(wa*wb for a,wa in law[0].items() for b,wb in law[0].items()
                         if all(passes(add(x,y),param) for x,y in zip(a,b)))
            assert levels[2][1]==den**2
            assert direct==sum(w for t,w in levels[2][0].items() if all(passes(x,param) for x in t))
    choices = [(5,a,b) for a in range(5) for b in range(5)]
    sites,trace = extract(5,1,mesh,labels,choices)
    assert sites and len(trace)==2 and len(sites)>=trace[-1] and clean(sites)==sites
    # A two-block example with a small prescribed alphabet exercises the same
    # selection for a nontrivial partially coloured input.
    s2,tr2 = extract(8,2,mesh,labels,[(7,1,0),(7,2,3),(7,3,1),(7,4,5)])
    assert s2 and len(tr2)==3 and clean(s2)==s2 and len(s2)>=tr2[-1]
    # Use a genuine dominating alphabet, compressing choices with identical
    # phase strings. Maxima depend only on support, irrespective of weights.
    p,n = 127,5
    full=[(p,a,b) for a in range(p) for b in range(p)]
    ref=Counter()
    for t,w in phase_cells(mesh): ref[t]+=w
    for gap in (1,2):
        ct=Counter(tuple(phase(opt,1+j*gap,mesh) for j in range(3)) for opt in full)
        for t,w in ref.items():
            ratio = Q(ct[t]*4*mesh**2,w*p*p)
            assert ratio**2<=1+Q(1,9)
    marg=Counter(phase(opt,1,mesh) for opt in full)
    assert all(Q(ct*mesh,p*p)**2 >= 1-Q(1,9) for ct in marg.values())
    reps={tuple(phase(opt,i,mesh) for i in range(1,n+1)):opt for opt in full}
    s3,tr3=extract(n,2,mesh,labels,reps.values())
    assert clean(s3)==s3 and len(s3)>=tr3[-1] and all(a<=b for a,b in zip(tr3,tr3[1:]))
    print('Two certified conditional steps,',len(reps),'scalar patterns, estimator',tr3,'set',s3)
    print('Exact Haar convolutions and finite extraction:',sites,s2)

def geometry(path):
    sys.path.insert(0,str(Path(path).resolve()))
    from tents import TentTable
    from verifica_parametro import J, V, Surd, half, q
    grid = 100000
    g = TentTable(64,grid)
    assert g.at(54500,12500)[2] and g.at(0,0) is None
    assert g.at(50000,12500) is None
    good = 0
    # Independent floating evaluation of the complete source series with an
    # analytic tail bound; check only ticks and scores separated from ties.
    import math
    def real(x):
        x=Surd.lift(x)
        return float(x.a)+float(x.b)*math.sqrt(2)
    j0,v0 = real(J),real(V)
    rng=Random(2048)
    for _ in range(120):
        i,j = rng.randrange(grid),rng.randrange(grid)
        val = g.at(i,j)
        if val is None:
            continue
        s=i/grid; t=j/grid-(j/grid>=0.5); u=s-0.5
        e=t if u<0 else 2*t-math.copysign(0.5,t)
        den=1.5-e
        w=max(0,-u,u-v0)
        comp=0.
        for k in range(80):
            left=v0-(v0-j0)*2**(-k); right=v0-(v0-j0)*2**(-k-1)
            comp+=2*(right-left)*max(0,u-(left+right)/2)
            if left<u<right: w=min(u-left,right-u)
        f=g.K*(2*s*s-(59/60-15/8/3)*s+15/8*(comp+w*w/den))+(e+0.5)**2
        f+=8/float(g.tau)*sum(max(0,s-real(z)) for z in g.cusps)
        score=64**2*math.log2(max(1,g.H*math.sqrt(15/8)*w/den**1.5))
        if abs(f*grid-round(f*grid))>1e-5: assert val[0]==math.floor(f*grid)
        if score==0 or abs(score-round(score))>1e-7: assert val[1]==math.floor(score)
        assert val[2]==(.54<s<.55 and .12<t<.13)
        good+=1
    assert good>=15
    print(good,'retained exact endpoint features checked independently')

if __name__ == '__main__':
    args=argparse.ArgumentParser()
    args.add_argument('geometry')
    path=args.parse_args().geometry
    atoms(); coloured(); tiny(); geometry(path)
