"""Independent verification of the smooth-base certificates. Python 3.9+."""
from math import gcd,isqrt,prod
from pathlib import Path
import sys
from resonance import possible


def small_prime(x):
    return x>=2 and all(x%d for d in range(2,isqrt(x)+1))


def prove_q(q,p):
    assert (q-1)%(14*p)==0
    if p*p<=q:
        assert small_prime(q)
    else:
        for a in range(2,q):
            if pow(a,q-1,q)==1 and gcd(pow(a,(q-1)//p,q)-1,q)==1:
                return
        raise AssertionError('prime certificate failed')


def divisors(n):
    d=2
    while d*d<=n:
        if n%d==0:
            yield d
            while n%d==0:n//=d
        d+=1
    if n>1:yield n


def generator(q,m):
    tests=list(divisors(m))
    return next(h for a in range(2,q) if (h:=pow(a,(q-1)//m,q)) and all(pow(h,m//d,q)!=1 for d in tests))


def slopes(p,q):
    z=generator(q,7)
    m=(q-1)//p
    v=[pow(z,i,q)-1 for i in (3,4,1,6,2,5)]
    c,d=v[:2]
    # t=b/(a+b). The case a+b=0 is certified by a separate trace test.
    points={-pow(c,-1,q)%q,-pow(d,-1,q)%q}
    h=1;step=generator(q,m)
    for i in range(m):
        if (c-h*d)%q:
            points.add((h-1)*pow(c-h*d,-1,q)%q)
        h=h*step%q
    for x in points-{0,1}:
        val=[pow((1+x*r)%q,m,q) for r in v]
        if p<=20000:
            assert any(w not in (0,1) for w in val),(p,q,x)
        else:
            pairs_ok=all(a==0 or b==0 or a==b for a,b in zip(val[::2],val[1::2]))
            assert not(pairs_ok and prod(val)%q in (0,1)),(p,q,x)


def trim(a):
    while a and a[-1]==0:a.pop()
    return a


def rem(a,b,q):
    a=a[:]
    lead=pow(b[-1],-1,q)
    while len(a)>=len(b):
        shift=len(a)-len(b)
        c=a[-1]*lead%q
        for j,v in enumerate(b):a[shift+j]=(a[shift+j]-c*v)%q
        trim(a)
    return a


def polygcd(a,b,q):
    while b:a,b=b,rem(a,b,q)
    return a


def exp_poly(a,n,f,q):
    def mul(u,v):
        w=[0]*(len(u)+len(v)-1)
        for i,s in enumerate(u):
            for j,t in enumerate(v):w[i+j]+=s*t
        return rem(trim([s%q for s in w]),f,q)
    out=[1]
    while n:
        if n%2:out=mul(out,a)
        n//=2
        if n:a=mul(a,a)
    return out


def minus(a,k,q):
    a=a[:]
    a.extend([0]*max(0,k+1-len(a)))
    a[k]=(a[k]-1)%q
    return trim(a)


def has_three(q,A,B,C):
    # All x-coordinates of nonzero 3-torsion are roots of the 3-division polynomial.
    psi=[(4*A*C-B*B)%q,12*C%q,6*B%q,4*A%q,3]
    first=polygcd(psi,minus(exp_poly([0,1],q,psi,q),1,q),q)
    if len(first)<2:return 0
    rhs=[C%q,B%q,A%q,1]
    sq=minus(exp_poly(rhs,(q-1)//2,first,q),0,q)
    return int(len(polygcd(first,sq,q))>1)


def exact_trace(q,coefs):
    A,B,C=coefs
    sq=bytearray(q)
    for y in range(1,(q+1)//2):sq[y*y%q]=1
    return q-sum(1 if not (v:=(((x+A)*x+B)*x+C)%q) else 2*sq[v] for x in range(q))


def main():
    d=Path(__file__).resolve().parent
    limit=100000
    expected=possible(limit)
    assert expected==list(map(int,(d/'exponents.txt').read_text().split()))
    assert expected==list(map(int,(d/'independent-exponents.txt').read_text().split()))
    rows=[s.split() for s in (d/'certificates.txt').read_text().splitlines()]
    assert expected==[int(r[0]) for r in rows]
    tables=[d.parent/'units'/'auxiliary.txt',d.parent/'global-unit'/'auxiliary.txt']
    known={p:(q,a,b) for p,q,a,b in (map(int,l.split()) for l in next(path for path in tables if path.is_file()).read_text().splitlines())}
    counts={}
    for sp,kind,sq,sa,sb in rows:
        p,q,a,b=map(int,[sp,sq,sa,sb]);assert q>limit and q>p
        counts[kind]=counts.get(kind,0)+1
        if kind=='table':
            assert known[p]==(q,a,b) and (a-b)%p!=0
            continue
        prove_q(q,p)
        slopes(p,q)
        if kind=='three':
            assert p*p>16*q and a!=b
            assert (has_three(q,-1,-2,1),has_three(q,-4,-11,43))==(a,b)
        else:
            assert kind=='trace' and (a-b)%p!=0
            assert (exact_trace(q,(-1,-2,1)),exact_trace(q,(-4,-11,43)))==(a,b)
    print(len(rows),'exponents; maximum',max(expected),'counts',counts)


if __name__=='__main__':main()
