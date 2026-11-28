"""Independent exact sampling checks for the three-dimensional weighted transfer."""
from collections import Counter
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import product
from random import Random
from sys import argv
from block import Block
from finite import clean,extract,haar,phase,phase_cells
from weighted import cell_distance,feature,nested,score


def atom_test():
    mesh=2
    table={i:(sum(i),-1-i[0],i[1]==i[2]) if sum(i)!=3 else None
           for i in product(range(mesh),repeat=3)}
    scalar=[(i,j,(2*j-i+(2*y-4)//8)%mesh) for i in range(mesh) for j in range(mesh) for y in (1,3,5,7)]
    counts=Counter()
    for coords in product(scalar,repeat=3):
        key=tuple(table[idx] for idx in zip(*coords))
        if None not in key: counts[key]+=1
    (ones,d1),(triples,d3)=haar(table,mesh,3)
    assert d1==8 and d3==len(scalar)**3 and counts==triples
    assert ones==Counter((v,) for v in table.values() if v is not None)
    p,n,m=127,5,1
    full=[(p,a,b) for a in range(p) for b in range(p)]
    ref=Counter()
    for t,w in phase_cells(mesh):ref[t]+=w
    eps=F(1,(m+1)**2)
    for gap in (1,2):
        ct=Counter(tuple(phase(opt,1+y*gap,mesh) for y in range(3)) for opt in full)
        assert all(F(ct[t]*4*mesh**2,w*p*p)**3 <= 1+eps for t,w in ref.items())
    marg=Counter(phase(opt,1,mesh) for opt in full)
    assert all(F(ct*mesh,p*p)**3>=1-eps for ct in marg.values())
    reps={tuple(phase(opt,i,mesh) for i in range(1,n+1)):opt for opt in full}
    # A marked seed concentrated on the first coordinate yields an example with a genuine AP-free gain.
    test={idx:(int(idx[0]),0,idx[0]==0) for idx in table}
    chosen,trace=extract(n,m,mesh,test,reps.values(),3)
    assert clean(chosen)==chosen and len(chosen)>=trace[-1]>=trace[0] and len(chosen)>=3
    print('Haar triple microcells',d3,'finite estimator',trace,'selected',chosen)


def decimal_checks(b):
    mesh=1<<60;m=6;rng=Random(192)
    def dec(a):return D(a.numerator)/D(a.denominator)
    def T(x,w,g):return x*x+w*w*(g-1)/(5*(2-g))
    def w(x,r):
        j=int(r*x);return min(x-D(j)/r,D(j+1)/r-x)
    counts=[0,0,0];marks=0
    with localcontext() as ctx:
        ctx.prec=85
        for _ in range(1800):
            idx=tuple(rng.randrange(mesh) for _ in range(3));got=feature(b,m,mesh,idx)
            if got is None:continue
            z,s,t=[D(i)/mesh for i in idx]
            if z<D('.5'):
                x=s;angle=t if t<D('.5') else t-1
                if x<D('.5'):
                    angular=angle**2;kind=0
                else:
                    angular=(1+2*angle-(D('.5') if angle>0 else D('-.5')))**2;kind=1
                wz=w(z,2*b.k)
            else:
                h=int(4*b.k*(z-D('.5')));p=int((2*s%1)*b.n)
                x=((2*s-D(b.primary[h][1])/b.n)%1+1)%1
                a=((2*t-D(b.upper[p][h][1])/b.n)%1+1)%1
                angular=a*a;wz=w(z,4*b.k);kind=2
            wx=w(x,b.n);energy=T(z,wz,T(x,wx,angular/3));raw=m*m*(wz*wz*wx).ln()/D(2).ln()
            assert got[0]==int(energy*mesh)
            assert got[1]==int(raw.to_integral_value(rounding='ROUND_FLOOR'))
            assert got[2]==(D('60.25')<2*b.k*z<D('60.75'))
            if got[2]:marks+=1
            counts[kind]+=1
    assert min(counts)>25 and marks>0
    print('actual features in single, folded and upper charts',counts,'marked',marks)

if __name__=='__main__':
    if not __debug__:raise RuntimeError('checks require assertions')
    atom_test();decimal_checks(Block(argv[1]))
