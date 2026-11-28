"""Verify the S-unit square classes in the degree-21 field, using exact integers."""
import json
from math import isqrt
from pathlib import Path

P = [0]*22
P[0], P[7], P[14], P[21] = 8,-16,2,1
F = [1,-4,1,1]
FACTORS13 = [[8,1],[12,2,1],[12,4,1],[12,12,1]]


def remainder(poly, monic, q):
    h = [a % q for a in poly]
    for i in range(len(h)-1,len(monic)-2,-1):
        v = h[i]
        for j,c in enumerate(monic):
            h[i-len(monic)+1+j] = (h[i-len(monic)+1+j]-v*c) % q
    return h[:len(monic)-1]


def multiply(poly, other):
    result = [0]*(len(poly)+len(other)-1)
    for i,a in enumerate(poly):
        for j,b in enumerate(other):
            result[i+j] += a*b
    return result


def value(poly,x,q):
    y = 0
    for a in reversed(poly):
        y = (y*x+a) % q
    return y


def determinant(matrix):
    # Fraction-free Gaussian elimination over the integers.
    m = [row[:] for row in matrix]
    sign = prev = 1
    for k in range(len(m)-1):
        if not m[k][k]:
            pivot = next(j for j in range(k+1,len(m)) if m[j][k])
            m[pivot],m[k] = m[k],m[pivot]
            sign *= -1
        c = m[k][k]
        for i in range(k+1,len(m)):
            for j in range(k+1,len(m)):
                num = c*m[i][j]-m[i][k]*m[k][j]
                assert num % prev == 0
                m[i][j] = num//prev
        prev = c
    return sign*m[-1][-1]


def norm_numerator(poly):
    columns = []
    col = poly[:]
    for _ in range(21):
        columns.append(col)
        c = col[-1]
        col = [a-c*b for a,b in zip([0]+col[:-1],P[:-1])]
    return determinant(columns)  # determinant unchanged by transposition


def local_fields():
    for p in (2,7):
        assert all(value(F,j,p) for j in range(p))
    a = [0,2,0]
    v = [1,0,0]
    for _ in range(343):
        v = remainder(multiply(v,a),F,49)
    delta = [(s-t)%49 for s,t in zip(v,a)]
    assert all(c%7 == 0 for c in delta) and any(delta)
    product = [1]
    for f in FACTORS13:
        product = multiply(product,f)
        if len(f)==3:
            assert all(value(f,j,13) for j in range(13))
    assert [x%13 for x in product] == [5,0,0,0,0,0,0,1]
    return delta


def unit_characters(elements):
    pivots = {}
    witnesses = []
    for q in range(3,2000,2):
        if q in (7,13) or any(q%d==0 for d in range(2,isqrt(q)+1)):
            continue
        for r in range(q):
            if value(P,r,q):
                continue
            mask = 0
            for i,(den,coeff,_) in enumerate(elements):
                val = value(coeff,r,q)*pow(den,-1,q) % q
                symbol = pow(val,(q-1)//2,q)
                assert symbol in (1,q-1)
                if symbol != 1:
                    mask |= 1 << i
            word = mask
            while word:
                bit = word.bit_length()-1
                if bit not in pivots:
                    pivots[bit] = word
                    witnesses.append((q,r,mask))
                    break
                word ^= pivots[bit]
            if len(pivots)==len(elements):
                return witnesses
    raise ArithmeticError('Character matrix did not have full rank')


def main():
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    rows = json.loads(Path(__file__).with_name('elements.json').read_text())
    assert len(rows)==18
    assert [abs(r[-1]) for r in rows] == [1]*12+[8,343,13,169,169,169]
    for den,coeff,norm in rows:
        assert len(coeff)==21 and den > 0
        assert all(c*2**(i//7)%den==0 for i,c in enumerate(coeff))
        assert norm_numerator(coeff)==norm*den**21
    print('Seven-adic Eisenstein check, coefficient differences mod 49:',local_fields())
    supports = []
    for _,coeff,_ in rows[14:]:
        matches = [i for i,f in enumerate(FACTORS13) if not any(remainder(coeff,f,13))]
        assert len(matches)==1
        supports += matches
    assert sorted(supports)==list(range(4)) and supports[0]==0
    print('Four distinct supporting prime ideals at 13:',supports)
    w = unit_characters(rows[:12])
    print('Independent residue characters (q, root, bit mask):',w)
    print('Dimension certified: ordinary units mod squares = 12; S-units mod squares = 18.')


if __name__ == '__main__':
    main()
