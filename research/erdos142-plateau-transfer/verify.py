"""Independent direct-energy, row counting and exact progression checks."""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
from random import Random
import sys
from plateau import digit_witness, grid_for, import_engine, progression_free, solve


def check_packing():
    count = 0
    for n in range(1, 12):
        for mask in range(1 << n):
            sites = [i+1 for i in range(n) if mask & (1 << i)]
            direct = all(2*y-x not in sites for x, y in combinations(sites, 2))
            assert progression_free(n, sites) == direct
            count += 1
    for n in (255, 256, 257, 65535, 65536):
        assert progression_free(n, [1, n])
        assert not progression_free(n, [n-2, n-1, n])
    digits = {x-1 for x in digit_witness(182)}
    assert len(digits) == 28
    assert all(x == y == z for x, y, z in product(digits, repeat=3) if (x+z-2*y) % 182 == 0)
    return count


def direct_rows(grid, b, features):
    from verifica_parametro import F, G, J, R, V, Surd, q as slope, rr, ell
    m, prime = grid.m, grid.q
    half, zero = Q(1, 2), Surd(0)
    n = (m-1).bit_length()
    eps, gamma = Q(1, 128*m), Q(1, m*(n+2))
    ends = [V-(V-J)/2**i for i in range(n+1)]
    out = []
    for i in range(prime):
        s = Q(i, prime)
        u = s-half
        allowed = (0 < s < half-eps or eps < u < R)
        if not allowed or ends[-1] <= u <= V or min(abs(u-v) for v in [*ends, V]) <= gamma:
            out.append(None)
            continue
        g = slope*max(zero, G-u)
        v = slope*max(zero, V-u)/2
        w = max(zero, -u) + max(zero, u-V)
        plateau = False
        if J < u < ends[-1]:
            lo, hi = next((l, r) for l, r in zip(ends, ends[1:]) if l < u < r)
            g = slope*(G-lo)
            v -= slope*(u-lo)/2
            w = (u-lo)*(hi-u)
            plateau = True
        if u < 0:
            arcs = [(-min(ell(s), half-rr(s)), rr(s), 'L')]
        else:
            arcs = [(rr(u), half-ell(u)-max(slope*max(zero, F-u), v), '+'),
                    (rr(u)-half+g, -ell(u)-v, '-')]
        arcs = [(lo+eps, hi-eps, sheet) for lo, hi, sheet in arcs]
        cusp = 8*sum(abs(u-v) for v in [*ends, V])/gamma
        h0 = grid.K*s*s+cusp
        hf = grid.K*s*s+Q(features.floor_surd(cusp*grid.D), grid.D)
        j = next((k for k in range(grid.h) if w*2**k >= 1), grid.h)
        label = -1 if w == 0 else grid.h-2*j-2 if j < grid.h else -grid.h-1
        out.append((s, arcs, label, h0, hf, w, plateau))
    return out


def point(rows, grid, b, i, j, features):
    row = rows[i]
    if row is None:
        return None
    s, arcs, label, h0, hf, w, plateau = row
    q, d = grid.q, grid.D
    t = Q(j if j*2 < q else j-q, q)
    for lo, hi, sheet in arcs:
        if lo < t < hi:
            e = t if sheet == 'L' else 2*t + (Q(-1, 2) if sheet == '+' else Q(1, 2))
            den = Q(3, 2)-e
            height = 16*(h0+(1+e)**2) + (grid.K//2**b)*(2*s+w*w/den)
            rounded = 16*(hf+(1+e)**2) + (grid.K//2**b)*(
                2*s+Q(features.floor_surd(w*w*d),d)*Q(d//den,d))
            assert 0 <= height-rounded <= Q(3*grid.K,d)
            energy = rounded*grid.scale
            assert energy.denominator == 1
            return label, int(energy), height, w, plateau
    return None


def check_grid(q, m, b, features, thorough):
    grid = grid_for(q, m, b, features)
    rows = direct_rows(grid, b, features)
    random = Random(250*q+m)
    samples = list(product(range(q), repeat=2)) if thorough else [
        (random.randrange(q), random.randrange(q)) for _ in range(3000)]
    # Inspect every allowed angular residue in a plateau row.
    if not thorough:
        samples += [(i, t) for i,row in enumerate(rows) if row and row[-1] for t in range(q)]
    points = {}
    def get(i, j):
        if (i,j) not in points:
            p = point(rows,grid,b,i,j,features)
            assert grid.point(i,j) == (p[:2] if p else None)
            points[i,j] = p
        return points[i,j]
    for i,j in samples:
        get(i,j)
    if thorough:
        for i in range(q):
            block = [p for j in range(q) if (p:=get(i,j))]
            sums = (len(block),sum(p[0] for p in block),sum(p[1] for p in block),
                    sum(p[0]**2 for p in block),sum(p[1]**2 for p in block))
            assert grid.partial(i,0,q) == sums
    valid = [k for k,p in points.items() if p]
    plateau_points = [k for k in valid if points[k][-1]]
    if not thorough:
        assert plateau_points
    pairs = combinations(valid,2) if thorough else ((random.choice(plateau_points), random.choice(valid)) for _ in range(4200))
    triples = touched = 0
    for x,z in pairs:
        if x == z:
            continue
        y = tuple((i+j)*((q+1)//2)%q for i,j in zip(x,z))
        middle = get(*y)
        if not middle:
            continue
        a,c = points[x], points[z]
        ds = Q(x[0]-z[0],q)
        t = (2*(x[1]-z[1]))%q
        dt = Q(min(t, q-t),q)
        delta = a[2]+c[2]-2*middle[2]
        assert grid.K*ds*ds + (1+grid.K*a[3]*a[3])*dt*dt <= (1 << (2*b+8))*delta
        triples += 1
        touched += int(a[-1] or c[-1] or middle[-1])
    return len(points),len(plateau_points),triples,touched


if __name__ == '__main__':
    engine=Path(sys.argv[1])
    construct, features=import_engine(engine)
    print('Exact AP checks on finite subsets:',check_packing(),flush=True)
    for q,m,b,thorough in ((17,2,3,True),(23,3,3,True),(257,64,5,False)):
        print('Grid, plateau points, triples, triples touching plateaus:',check_grid(q,m,b,features,thorough),flush=True)
    for n in (64,182,300):
        result=solve(n,engine)
        assert result['sites'] and progression_free(n,result['sites'])
        print(n,result['method'],len(result['sites']),flush=True)
