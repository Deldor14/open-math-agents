"""Find a split auxiliary prime certifying pure cyclotomic p-th powers.

The optional first argument is the upper bound, the second the PARI/GP binary.
The other verifier uses only the standard library and does not use PARI.
"""
from math import isqrt
import subprocess
import sys


def factors(n):
    ans = []
    d = 2
    while d*d <= n:
        if n%d == 0:
            ans.append(d)
            while n%d == 0:
                n //= d
        d += 1
    if n > 1:
        ans.append(n)
    return ans


def prime(n):
    return n >= 2 and all(n%d for d in range(2, isqrt(n)+1))


def generator(q):
    divs = factors(q-1)
    return next(g for g in range(2,q) if all(pow(g,(q-1)//s,q)!=1 for s in divs))


def eligible(p,q):
    g = generator(q)
    m = (q-1)//p
    z = [pow(g,i*((q-1)//7),q) for i in range(1,7)]
    # The first conjugate ratio cuts the projective line down to at most m+2.
    subgroup = {pow(g,p*i,q) for i in range(m)}
    assert len(subgroup) == m
    cases = {-z[0]%q,-z[5]%q}
    for h in subgroup-{1}:
        cases.add((z[0]-h*z[5])*pow(h-1,-1,q)%q)
    for t in cases-{0,q-1}:
        w = [(t+zi)%q for zi in z]
        if any(a and b and pow(a,m,q)!=pow(b,m,q) for a,b in zip(w[:3],w[::-1])):
            continue
        # At Q=0 the unit test is omitted. At the remaining slopes Q/D^6
        # is a p-th power, with Q(t,1)=(t^7+1)/(t+1).
        if (pow(t,7,q)+1)%q and pow((pow(t,7,q)+1)*pow(t+1,-7,q)%q,m,q)!=1:
            continue
        return False
    # Character vectors of the two fundamental units must be independent.
    h = pow(g,m,q)
    logs = {}
    a = 1
    for i in range(p):
        logs[a] = i
        a = a*h%q
    cols = [(logs[pow(1+r,m,q)],logs[pow(1+r*r,m,q)]) for r in z]
    return any((a*d-b*c)%p for a,b in cols for c,d in cols)


def main():
    bound = int(sys.argv[1]) if len(sys.argv)>1 else 20000
    gp = sys.argv[2] if len(sys.argv)>2 else 'gp'
    with subprocess.Popen([gp,'-fq'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as proc:
        proc.stdin.write('E=ellinit([0,-1,0,-2,1]);F=ellinit([0,-4,0,-11,43]);\n')
        for p in range(11,bound+1,2):
            if not prime(p):
                continue
            k = 0
            while True:
                k += 1
                q = 14*p*k+1
                if not prime(q) or not eligible(p,q):
                    continue
                proc.stdin.write(f'print(ellap(E,{q})," ",ellap(F,{q}))\n')
                proc.stdin.flush()
                e, f = map(int,proc.stdout.readline().split())
                if (e-f)%p:
                    print(p,q,e,f,flush=True)
                    break
        proc.stdin.close()


if __name__=='__main__':
    main()
