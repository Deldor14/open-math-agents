"""Independent characteristic-p Frobenius traces and geometric independence witnesses."""
from itertools import combinations
from math import isqrt

MODELS = [(-2106,702,42120,-16497), (-189,27,837,-270), (-270,-162,-1188,-783)]


def primes(limit):
    return [p for p in range(5,limit+1) if p != 13 and
            all(p % q for q in range(2,isqrt(p)+1))]


def weights(p):
    g = (p-1)//2
    factorial = [1]
    for i in range(1,g+1):
        factorial.append(factorial[-1]*i % p)
    values = []
    for u in range((g+1)//2,(p-1)//3+1):
        v,w = p-1-3*u, 2*u-g
        factors = factorial[u]*factorial[v]*factorial[w] % p
        values.append((v,w,factorial[g]*pow(factors,-1,p) % p))
    return values


def traces(p):
    terms = weights(p)
    roots = [h for h in range(p) if (h*h-h-3) % p == 0]
    if roots:
        def at(h,c):
            A,B = (c[0]+c[1]*h) % p, (c[2]+c[3]*h) % p
            return sum(n*pow(A,v,p)*pow(B,w,p) for v,w,n in terms) % p
        return [[at(h,c) for c in MODELS] for h in roots]

    def multiply(x,y):
        a,b=x
        c,d=y
        return ((a*c+3*b*d)%p,(a*d+b*c+b*d)%p)

    def powers(x,limit):
        table=[(1,0)]
        for _ in range(limit):
            table.append(multiply(table[-1],x))
        return table

    result=[]
    for a,b,c,d in MODELS:
        A = powers((a,b),max(v for v,w,n in terms))
        B = powers((c,d),max(w for v,w,n in terms))
        alpha=beta=0
        for v,w,n in terms:
            t,u=multiply(A[v],B[w])
            alpha += n*t
            beta += n*u
        result.append((alpha*alpha+alpha*beta-3*beta*beta) % p)
    return [result]


def split_counts(p):
    roots = [h for h in range(p) if (h*h-h-3) % p == 0]
    assert len(roots)==2
    squares = {x*x % p for x in range(1,p)}
    row=[]
    for a,b,c,d in MODELS:
        for h in roots:
            A,B=(a+b*h)%p,(c+d*h)%p
            values=[(x*(x*x+A)+B)%p for x in range(p)]
            row.append(-sum(0 if y==0 else 1 if y in squares else -1 for y in values))
    return row


if __name__ == "__main__":
    failed=[]
    tested=primes(5000)
    for p in tested:
        data=traces(p)
        if any(all(row[0]==row[j] for row in data) for j in (1,2)):
            failed.append(p)
    assert len(tested)==666 and failed==[3067]
    print("Characteristic-p test:",len(tested),"primes. Exception:",failed)
    small=[(p,split_counts(p)) for p in [79,131,311,599]]
    for p,row in small:
        print("Split witness",p,row)
    for i,j in combinations(range(6),2):
        assert any((row[i]==0)!=(row[j]==0) for _,row in small)
    print("All 15 geometric pairs distinguished by ordinary/supersingular reduction.")
