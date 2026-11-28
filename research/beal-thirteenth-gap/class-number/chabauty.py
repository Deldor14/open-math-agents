"""Check the 5-adic disk sieve and the tangent calculation modulo 25."""
from math import comb

M = 25


def product(a, b, modulus=M):
    result = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            result[i+j] = (result[i+j] + u*v) % modulus
    return result


def solve(rows):
    unknowns = len(rows)
    for i in range(unknowns):
        j = next(j for j in range(i,unknowns) if rows[j][i] % 5)
        rows[i], rows[j] = rows[j], rows[i]
        inv = pow(rows[i][i], -1, M)
        rows[i] = [v*inv % M for v in rows[i]]
        for j in range(unknowns):
            if j != i:
                scale = rows[j][i]
                rows[j] = [(v-scale*w) % M for v,w in zip(rows[j],rows[i])]
    return [row[-1] for row in rows]


def main():
    r = 12
    assert (r**3+r*r-4*r+1) % 25 == 0 and (3*r*r+2*r-4) % 5
    s = r*r-r+1
    assert (4*s) % 25 == 7 and (64*s**4*(r*r+r-5)) % 25 == 19
    assert 4**6*s**7*pow(r,-2,M) % M == (36-7**7) % M
    affine = [(x,y) for x in range(5) for y in range(5) if (y*y-x**7-3)%5 == 0]
    surviving = [(x,y) for x,y in affine
                 if (x-3 if x != 3 else 7*3**6)%5 in (1,4)]
    assert surviving == [(2,1),(2,4)]

    # z=x-X0, so y^2=f(z) and the branch at +P has y(0)=-6 modulo 25.
    f = [36] + [comb(7,i)*7**(7-i) for i in range(1,8)]
    y = [19]
    for i in range(1,12):
        other = sum(y[j]*y[i-j] for j in range(1,i))
        y.append(((f[i] if i < len(f) else 0)-other)*pow(2*y[0],-1,M) % M)

    # g+h*y vanishes to order 12 at P, h monic quartic, deg(g)<=7.
    rows = [[y[i-j] for j in range(4)] + [-y[i-4] % M] for i in range(8,12)]
    h = solve(rows) + [1]
    hy = product(h,y)
    g = [(-c) % M for c in hy[:8]]
    assert hy[8:12] == [0]*4
    lhs, square = product(product(h,h),f), product(g,g)
    norm = [(a-(square[i] if i < len(square) else 0)) % M for i,a in enumerate(lhs)]
    assert norm == [0]*12 + [15,5,15,1]
    assert [v % 5 for v in h[:4]] == [0,0,0,1]
    assert [v % 5 for v in g[:4]] == [0,0,0,1]

    # In F_5[z]/(z^3), inverse of 2*v_3, followed by -du/(2*v_3).
    inv = [2,2,1]
    assert product([2*c for c in y[:3]],inv,5)[:3] == [1,0,0]
    tangent = product([-(v//5) for v in norm[12:15]], inv, 5)[:3]
    x_power = [1]
    line = []
    for _ in range(3):
        line.append(product(x_power,tangent,5)[2])
        x_power = product(x_power,[2,1],5)
    assert line == [4,0,3] and (3*line[0]+line[2]) % 5 == 0
    assert (3+2**2) % 5 != 0
    print("finite disks",surviving,"plus infinity")
    print("h",h,"g",g,"residual cubic",norm[12:])
    print("log(9P)/5 mod 5",line,"annihilator mod 5: (3+x^2)dx/(2y)")


if __name__ == "__main__":
    main()
