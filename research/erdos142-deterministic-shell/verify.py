"""Independent checks of the selected orbit, finite objectives, and AP certificates."""
from itertools import combinations
from fractions import Fraction as Q
from pathlib import Path
import json

from verifica_parametro import Cell, R
from construct import grid, range_moments
from scores import correlation

HERE = Path(__file__).resolve().parent


def no_ap(xs):
    assert len(xs)==len(set(xs))
    members = set(xs)
    return all(2*y-x not in members for x,y in combinations(sorted(xs),2))


def rectangle(q,m):
    # Direct signed coordinate comparisons, without floor_surd or the range-sum formula.
    delta,half = Q(1,128*m),Q(1,2)
    table = {}
    for i in range(q):
        s = Q(i,q)
        if not 0 < s < half-delta and not half+delta < s < half+R:
            continue
        layers = ['L'] if s<half else ['+','-']
        for label in layers:
            lo,hi = Cell(None,None,label).edges(s)
            a,b = lo+delta,hi-delta
            for j in range(-q//2+1,q//2+1):
                t = Q(j,q)
                if a<t<b:
                    e = t if s<half else 2*t-(half if label=='+' else -half)
                    f = ((1024*m*s)**2 + (1+e)**2)*4*q*q
                    assert f.denominator==1
                    table[i,j%q] = int(f)
    return table


def verify_small(d):
    n,m,q = d['N'],d['m'],d['q']
    T = rectangle(q,m)
    energies = list(T.values())
    size, first, second = len(T), sum(energies), sum(x*x for x in energies)
    assert size==d['grid_size']
    _,mom = grid(q,m)
    for i in range(q):
        row = [f for (s,t),f in T.items() if s==i]
        assert (len(row),sum(row),sum(f*f for f in row))==mom[i]

    # All q^2 candidate shifts evaluated directly. Check both conditional choices.
    alive = dict.fromkeys(range(1,n+1),0)
    variance = size*second-first**2
    cap = 4*m*(size*4*q*q*(1024*m)**2)**2
    for j,((u,w),(hs,ht)) in enumerate(zip(d['direction'],d['shifts']),1):
        v = pow(2,-1,q)*w%q
        def shifted(h,k):
            out = {}
            for x,c in alive.items():
                key = (x*u+h)%q,(x*v+k)%q
                if key in T:
                    out[x] = c + size*T[key]-first
            return out
        scores = [[sum(cap-c*c-(m-j)*variance for c in shifted(h,k).values())
                   for k in range(q)] for h in range(q)]
        assert hs==max(range(q),key=lambda h:sum(scores[h]))
        assert ht==max(range(q),key=scores[hs].__getitem__)
        alive = shifted(hs,ht)
    assert len(alive)==d['orbit_survivors']
    order = sorted(alive,key=lambda x:(alive[x],x))
    # Test each interval directly, with a different AP test.
    optimum = max(j-i for i in range(len(order)) for j in range(i+1,len(order)+1)
                  if no_ap(order[i:j]))
    assert len(d['core'])==optimum


def verify_output(d):
    n,m,q = d['N'],d['m'],d['q']
    xs=d['result']
    assert set(d['core'])<=set(xs)<=set(range(1,n+1))
    assert no_ap(xs)
    for x in set(range(1,n+1))-set(xs):
        assert not no_ap(xs+[x])
    def norm(d,u):
        r=d*u%q
        return min(r, q-r)
    assert min(sum((1024*m*norm(d,u))**2 + norm(d,w)**2 for u,w in d0)
               for d0 in [d['direction']] for d in range(1,n)) == d['squared_min_numerator']


def verify_operations():
    for n in range(1,70):
        for a,b in (([1]*n,[10**20*i for i in range(n)]),
                    ([i*i-4*i-7 for i in range(n)],[(-1)**i*(93*i+1) for i in range(n)])):
            assert correlation(a,b)==[sum(a[i]*b[(i+h)%n] for i in range(n)) for h in range(n)]
        for k in range(5):
            assert range_moments(n,[(i-3)**k for i in range(k+1)])==sum((i-3)**k for i in range(n))


if __name__=='__main__':
    verify_operations()
    witnesses=json.loads((HERE/'witnesses.json').read_text())
    for d in witnesses:
        verify_output(d)
        if d['N'] in (4,61):
            verify_small(d)
        print(d['N'],len(d['core']),len(d['result']),'verified')
