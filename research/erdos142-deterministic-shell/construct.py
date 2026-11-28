"""Deterministic construction for [1,N]. Only the Python standard library is needed."""
import argparse
from fractions import Fraction
from math import comb, isqrt, lcm

from verifica_parametro import Cell, R, Surd
from scores import first_shift_scores, powers_of_generator, product_scores, second_shift_scores

AREA = Surd(Fraction(17, 28), Fraction(-3, 14))


def floor_surd(value):
    v = Surd.lift(value)
    den = lcm(v.a.denominator, v.b.denominator)
    a, b = int(v.a * den), int(v.b * den)
    radical = isqrt(2 * b * b)
    if b < 0:
        radical = -radical - 1
    return (a + radical) // den


def ceil_root(n, degree):
    lo, hi = 0, 1
    while hi**degree < n:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**degree >= n:
            hi = mid
        else:
            lo = mid
    return hi


def dimension(n):
    power, best, chosen = Surd(1), Surd(0), 1
    for m in range(1, n.bit_length() + 1):
        power = power * AREA * AREA
        score = power / (m * ceil_root(n, 2*m)**4)
        if score > best:
            best, chosen = score, m
    return chosen


def next_prime(n):
    limit = 2*max(2,n)
    sieve = bytearray([1])*(limit+1)
    for i in range(2,isqrt(limit)+1):
        if sieve[i]:
            sieve[i*i::i] = bytes((limit-i*i)//i+1)
    return next(q for q in range(max(3,n+1),limit+1) if sieve[q])


def kernel(q, a, b, dyadic):
    # Upward dyadic rounding of 1/(1+(a/b)*||j/q||^2).
    constant = b*q*q
    weights = []
    for j in range(q):
        den = constant + a*min(j, q-j)**2
        weights.append((dyadic*constant + den-1)//den)
    return weights


def energy(i, t, layer, q, K):
    term = 2*q + 2*t if layer == 'L' else 2*q + 4*t + (q if layer == '-' else -q)
    return 4*K*i*i + term*term


def range_moments(n, values):
    """Sum a polynomial on n successive integers from its first d+1 values."""
    total = 0
    for order in range(1, len(values) + 1):
        total += values[0] * comb(n, order)
        values = [y-x for x,y in zip(values, values[1:])]
    return total


def grid(q, m):
    eps = Fraction(1, 128*m)
    K = (1024*m)**2
    rows, counts = [], []
    for i in range(q):
        s = Fraction(i, q)
        intervals = []
        if 0 < s < Fraction(1, 2)-eps:
            layers = ('L',)
        elif Fraction(1, 2)+eps < s < R+Fraction(1, 2):
            layers = ('+', '-')
        else:
            layers = ()
        moments = [0, 0, 0]
        for layer in layers:
            low, high = Cell(None, None, layer).edges(s)
            lo = floor_surd((low+eps)*q) + 1
            hi = -floor_surd((eps-high)*q) - 1
            if lo > hi:
                continue
            intervals.append((lo, hi, layer))
            sample = [energy(i,lo+j,layer,q,K) for j in range(5)]
            width = hi-lo+1
            moments[0] += width
            moments[1] += range_moments(width, sample[:3])
            moments[2] += range_moments(width, [v*v for v in sample])
        rows.append(intervals)
        counts.append(tuple(moments))
    return rows, counts


def select_grid(n, m):
    B, H = ceil_root(n, 2*m), 1024*m
    q = next_prime(n)
    while True:
        scale = 1 << q.bit_length()
        primary = kernel(q,1024*B*B*H,1,scale)
        secondary = kernel(q,1024*B*B,H,scale)
        if (n-1)*(4*sum(primary)*sum(secondary))**m < (q*scale)**(2*m):
            rows, counts = grid(q,m)
            density = Fraction(sum(row[0] for row in counts), q*q)
            if Surd.lift(density) >= AREA*(1-Fraction(1,5*m)):
                return q, primary, secondary, rows, counts
        q = next_prime(2*q)


def direction(n, m, q, primary, secondary):
    weights = [1]*(n-1)
    answer = []
    powers = powers_of_generator(q)
    for kernel_values in (primary, secondary)*m:
        # The unused coordinates contribute the same positive factor for every choice.
        scores = product_scores(weights,kernel_values,powers)
        h = min(range(q), key=scores.__getitem__)
        for d in range(1,n):
            weights[d-1] *= kernel_values[(d*h)%q]
        answer.append(h)
    return list(zip(answer[::2],answer[1::2]))


def translate(n, q, vectors, rows, counts):
    m = len(vectors)
    K = (1024*m)**2
    size, first, second = map(sum,zip(*counts))
    # Energies have been multiplied by 4q^2. Centered energies below
    # use an additional factor size, keeping all moments and scores integral.
    variance = size*second - first*first
    limit = 4*m*(size*4*q*q*K)**2
    row_stats = [(c, size*s-first*c, size*size*t-2*size*first*s+first*first*c)
                 for c,s,t in counts]
    alive = {i:0 for i in range(1,n+1)}
    shifts = []
    for j,(u,w) in enumerate(vectors,1):
        v = w*pow(2,-1,q)%q
        fixed = limit - (m-j)*variance
        points = [(i,c,i*u%q,i*v%q) for i,c in alive.items()]
        row_scores = first_shift_scores(q,points,row_stats,fixed)
        hs = max(range(q),key=row_scores.__getitem__)
        def updated(ht):
            for i,c,s,t in points:
                idx = (s+hs)%q
                signed_t = (t+ht+q//2)%q-q//2
                for lo,hi,layer in rows[idx]:
                    if lo <= signed_t <= hi:
                        e = energy(idx,signed_t,layer,q,K)
                        yield i,c + size*e-first
                        break
        column_scores = second_shift_scores(q,points,rows,hs,fixed,
                            lambda i,t,layer: energy(i,t,layer,q,K),size,first)
        ht = max(range(q),key=column_scores.__getitem__)
        alive = dict(updated(ht))
        shifts.append((hs,ht))
    assert sum(limit-c*c for c in alive.values()) > 0
    return sorted((c,i) for i,c in alive.items()),size,shifts


def enlarge(n, core):
    selected = set(core)
    forbidden = set()
    def block(x,y):
        forbidden.update([2*x-y, 2*y-x])
        if (x+y)%2 == 0:
            forbidden.add((x+y)//2)
    old = []
    for x in core:
        for y in old:
            block(x,y)
        old.append(x)
    for x in range(1,n+1):
        if x in selected or x in forbidden:
            continue
        for y in selected:
            block(x,y)
        selected.add(x)
    return sorted(selected)


def certified_interval(points):
    """Largest contiguous interval in (energy, index) order containing no AP."""
    rank = {x:i for i,(c,x) in enumerate(points)}
    values = sorted(rank)
    lower = [0]*len(values)
    for j,z in enumerate(values):
        for i in range(j):
            x = values[i]
            if (x+z)%2:
                continue
            mid = rank.get((x+z)//2)
            if mid is not None:
                ranks = rank[x],mid,rank[z]
                right = max(ranks)
                lower[right] = max(lower[right], min(ranks)+1)
    left = best_left = best_right = 0
    for right, bound in enumerate(lower):
        left = max(left,bound)
        if right+1-left > best_right-best_left:
            best_left,best_right = left,right+1
    return sorted(x for c,x in points[best_left:best_right])


def construct(n,m=None,enhance=False):
    if n < 4:
        raise ValueError("N must be at least 4")
    if m is None:
        m = dimension(n)
    if not 1 <= m <= n.bit_length():
        raise ValueError("invalid dimension")
    q,primary,secondary,rows,counts = select_grid(n,m)
    vectors = direction(n,m,q,primary,secondary)
    K = (1024*m)**2
    def squared(d,v):
        t = d*v%q
        return min(t,q-t)**2
    minimum = min(sum(K*squared(d,u)+squared(d,w) for u,w in vectors) for d in range(1,n))
    B = ceil_root(n,2*m)
    assert 1024*B*B*minimum > 2*m*(1024*m)*q*q
    points,size,shifts = translate(n,q,vectors,rows,counts)
    # Points are sorted by size times total energy (scaled by 4q^2),
    # after a common translation. The longest valid window contains any valid bin.
    left = start = end = 0
    for right,(c,i) in enumerate(points):
        while 4*(c-points[left][0]) >= size*minimum:
            left += 1
        if right+1-left > end-start:
            start,end = left,right+1
    metric_core = sorted(i for c,i in points[start:end])
    core = certified_interval(points) if enhance else metric_core
    assert len(core) >= end-start > 0
    result = enlarge(n, core) if enhance else core
    return dict(N=n,m=m,q=q,direction=vectors,shifts=shifts,
                grid_size=size,squared_min_numerator=minimum,orbit_survivors=len(points),
                metric_window_size=end-start,enhanced=enhance,core=core,result=result)


if __name__ == '__main__':
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('N',type=int)
    parser.add_argument('--dimension',type=int)
    parser.add_argument('--enhance',action='store_true',
                        help='check all progressions for a larger energy interval, then extend greedily')
    args = parser.parse_args()
    print(json.dumps(construct(args.N,args.dimension,args.enhance)))
