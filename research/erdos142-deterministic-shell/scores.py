"""Exact cyclic correlations and piecewise polynomial range sums."""
from math import comb, isqrt


def correlation(x, y):
    """Return h -> sum_i x[i] y[(i+h) mod q] via one integer product."""
    q = len(x)
    if len(y) != q or not q:
        raise ValueError("equal nonempty arrays required")
    base_x, base_y = min(x), min(y)
    a = [k-base_x for k in x]
    b = [k-base_y for k in y]
    offset = base_x*sum(b) + base_y*sum(a) + q*base_x*base_y
    if max(a) == 0 or max(b) == 0:
        return [offset]*q
    size = max(1, (int(q*max(a)*max(b)).bit_length()+7)//8)
    def pack(values):
        return int.from_bytes(b''.join(k.to_bytes(size,'little') for k in values),'little')
    product = pack([a[0]] + a[:0:-1]) * pack(b)
    raw = memoryview(product.to_bytes(2*q*size,'little'))
    def digit(i):
        return int.from_bytes(raw[i*size:(i+1)*size],'little')
    return [digit(h)+digit(h+q)+offset for h in range(q)]


def powers_of_generator(q):
    value = q-1
    factors = set()
    for d in range(2,isqrt(value)+1):
        while value%d == 0:
            factors.add(d)
            value //= d
    if value > 1:
        factors.add(value)
    g = next(k for k in range(2,q) if all(pow(k,(q-1)//p,q)!=1 for p in factors))
    powers = [1]
    for _ in range(q-2):
        powers.append(powers[-1]*g%q)
    return powers


def product_scores(weights, kernel, powers):
    """weights[d-1] is the coefficient of the nonzero residue d."""
    weights_pad = [0]+weights+[0]*(len(kernel)-len(weights)-1)
    values = correlation([weights_pad[d] for d in powers],[kernel[d] for d in powers])
    scores = [kernel[0]*sum(weights)]*len(kernel)
    for d,x in zip(powers,values):
        scores[d] = x
    return scores


def first_shift_scores(q,points,row_stats,fixed):
    buckets = [[0]*q for _ in range(3)]
    for i,c,s,t in points:
        buckets[0][s] += fixed-c*c
        buckets[1][s] -= 2*c
        buckets[2][s] -= 1
    values = [correlation(x,y) for x,y in zip(buckets,zip(*row_stats))]
    return list(map(sum,zip(*values)))


def second_shift_scores(q, points, rows, hs, fixed, energy_fn, size, first):
    # Newton coefficients in the global basis binomial(h,k) are constant
    # on each arc. Two difference-array updates add them over the whole arc.
    diff = [[0]*5 for _ in range(q+1)]
    for i,c,s,t in points:
        idx = (s+hs)%q
        for lo,hi,layer in rows[idx]:
            for wrap in range(3):
                offset = t-wrap*q
                left,right = max(0,lo-offset),min(q-1,hi-offset)
                if left > right:
                    continue
                vals = [fixed-(c+size*energy_fn(idx,h+offset,layer)-first)**2 for h in range(5)]
                for k in range(5):
                    diff[left][k] += vals[0]
                    diff[right+1][k] -= vals[0]
                    vals = [b-a for a,b in zip(vals,vals[1:])]
    totals = [0]*5
    scores = []
    for h in range(q):
        for k in range(5):
            totals[k] += diff[h][k]
        scores.append(sum(totals[k]*comb(h,k) for k in range(5)))
    return scores
