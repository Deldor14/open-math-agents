"""Exact finite certificates. All calculations use only the Python standard library."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt

def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

def nextprime(n):
    p=max(n+1,3)
    while not prime(p):
        p+=1
    return p

def contains_ap(A,k,D):
    chosen=set(A)
    return any(all(x+i*d in chosen for i in range(1,k)) for x in chosen for d in D)

def extremal_seed(n,k):
    for size in range(n,-1,-1):
        for A in combinations(range(n),size):
            if not contains_ap(A,k,range(1,(n-1)//(k-1)+1)):
                return A

def transfer(k,D,seed,n,N):
    """Construct a D-free set by exact averaging over the cyclic offset."""
    D=set(D);q=2*n-1
    assert k>=3 and n>=2 and D and min(D)>0 and len(D)<q*(k-1)
    assert set(seed)<=set(range(n)) and not contains_ap(seed,k,range(1,(n-1)//(k-1)+1))
    p=nextprime(max(D))
    radial=lambda d:min(d%p,(-d)%p)
    a=next(a for a in range(1,p) if all(2*q*(k-1)*radial(a*d)>=p for d in D))
    period=2*p*q
    delta={0:0,period:0}
    def add(left,right):
        delta[left]=delta.get(left,0)+1
        delta[right]=delta.get(right,0)-1
    for x in range(N):
        for s in seed:
            left=(2*p*s-2*q*a*x)%period
            end=left+p
            if end<=period:
                add(left,end)
            else:
                add(left,period);add(0,end-period)
    best=offset=count=0
    for b,change in sorted(delta.items()):
        count+=change
        if count>best:
            best,offset=count,b
    def allowed(x):
        label,err=divmod((2*q*a*x+offset)%period,2*p)
        return label in seed and err<p
    S=[x for x in range(N) if allowed(x)]
    assert len(S)==best and 2*q*best>=N*len(seed) and not contains_ap(S,k,D)
    return S

def two_step_phase(k,a,b):
    """A rotation giving density (k-1)^2/(k^2-k+1) for two steps and prime k."""
    assert prime(k) and a>0 and b>0 and a!=b
    g=gcd(a,b)
    a,b=a//g,b//g
    if a%k and b%k:
        return F(1,k*g)
    if a%k:
        a,b=b,a
    assert a%k==0 and gcd(b,k)==1
    # b*j-a*i=1 with i=1 (mod k). b=1 imposes no congruence on i.
    i=1 if b==1 else 1+k*((-(a+1)*pow(a*k,-1,b))%b)
    j=(1+a*i)//b
    assert b*j-a*i==1 and (i-1)%k==0 and gcd(j,k)==1
    L=k*k-k+1
    theta=max((F(j,k)-F(1,k*L))/a,F(i,k*b))
    assert theta<=F(j,k*a) and b*theta<=F(i,k)+F(k-1,k*L)
    return (theta/g)%1

def largest_gap(k,d,theta):
    q=theta.denominator;h=d*theta.numerator
    pts=sorted(set((i*h)%q for i in range(k)))
    return F(max([b-a for a,b in zip(pts,pts[1:])]+[q-pts[-1]]),q)

def verify_two():
    count=0
    for k in (2,3,5,7,11,13,17,19,23,29,31):
        L=k*k-k+1
        for a,b in combinations(range(1,65),2):
            theta=two_step_phase(k,a,b)
            assert max(largest_gap(k,a,theta),largest_gap(k,b,theta))<=F(k,L)
            count+=1
        # A sharp periodic word for (1,k), valid without primality.
    for k in range(2,101):
        L=k*k-k+1
        holes={(k-1)*j for j in range(k)}
        assert len(holes)==k
        for d in (1,k):
            ordered=sorted((h*pow(d,-1,L))%L for h in holes)
            assert max([b-a for a,b in zip(ordered,ordered[1:])]+[L-ordered[-1]])<=k
    return count

def brute_blocks():
    tested=0
    for k in (2,3,4,5):
        L=k*k-k+1
        # With fewer than k holes, adding holes up to k-1 preserves avoidance.
        for holes in combinations(range(L),k-1):
            A=set(range(L)).difference(holes)
            assert contains_ap(A,k,[1,k])
            tested+=1
    assert len(extremal_seed(8,3))==4
    return tested

def verify_transfer():
    tests=0
    for k in range(3,7):
        for n in (4,6,8):
            seed=extremal_seed(n,k)
            for D in ((2,),(1,7),(2,3,11),(11,19,23),(26,39,52,65)):
                for N in (23,64,99):
                    transfer(k,D,seed,n,N);tests+=1
    return tests

if __name__=='__main__':
    print('prime-length pair phases checked:',verify_two())
    print('sharp block hole patterns checked:',brute_blocks())
    print('finite all-step-set transfers checked:',verify_transfer())
