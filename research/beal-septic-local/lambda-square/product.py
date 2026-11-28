"""Directly multiply the Fermat-cover functions modulo pi^(p-1), with a dual-number argument."""
from math import comb
from pathlib import Path


def conv(a,b,p):
    n = p-1
    return [sum(a[i]*b[k-i] for i in range(k+1))%p for k in range(n)]


def add(a,b,p):
    return [(x+y)%p for x,y in zip(a,b)]


def scale(a,k,p):
    return [k*x%p for x in a]


def inverse(a,p):
    values = [pow(a[0], -1, p)]
    for k in range(1,p-1):
        values.append(-values[0]*sum(a[j]*values[k-j] for j in range(1,k+1))%p)
    return values


def evaluate(p,t,qT):
    zero = [0]*(p-1)
    one = [1]+zero[1:]
    def times(a,b):
        return conv(a[0],b[0],p), add(conv(a[0],b[1],p),conv(a[1],b[0],p),p)
    ans = one,zero
    for i in range(1,p):
        # Factor i*(1-zeta^i*x)/((1-x)*((zeta^i-1)/pi)) at x=t+epsilon.
        zeta_i = [comb(i,j)%p if j<=i else 0 for j in range(p-1)]
        denominator = [comb(i,j+1)%p if j+1<=i else 0 for j in range(p-1)]
        inv = scale(inverse(denominator,p),i,p)
        value = scale(add(one,scale(zeta_i,-t,p),p),pow(1-t,-1,p),p)
        derivative = scale(add(one,scale(zeta_i,-1,p),p),pow(1-t,-2,p),p)
        term = conv(value,inv,p), conv(derivative,inv,p)
        n = i
        while n:
            if n%2: ans = times(ans,term)
            n //= 2
            if n: term = times(term,term)
    value,diff = ans
    assert value[:-1]==one[:-1] and diff[:-1]==zero[:-1]
    c,d = value[-1],diff[-1]
    # Compare the two coefficients with those of (pi/(x-t))^(p*(p-2)).
    Q = -t*qT%p
    return c,d,(Q*d+2*c)%p


if __name__ == '__main__':
    rows = [tuple(map(int,s.split())) for s in Path(__file__).with_name('certificates.txt').read_text().splitlines()]
    for p,model,theta,t,qT,qu,minor,trace,ob in rows:
        if p>90: break
        c,d,defect = evaluate(p,t,qT)
        assert defect and defect*(1-t)%p==ob
        print(p, 'coefficient', c, 'derivative', d, 'power obstruction', defect)
