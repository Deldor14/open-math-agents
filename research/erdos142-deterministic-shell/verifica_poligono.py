"""Certificato geometrico esatto per il blocco di area 579/1904.
Uso: python3 verifica_poligono.py. Richiede soltanto la libreria standard.
Ogni cella è un trapezio aperto. La prova sul toro usa estremi razionali
di funzioni affini su poligoni convessi, senza arrotondamenti o campionamento.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product

half = Q(1, 2)
R = Q(50, 119)


def right(x):
    return 69*x/112


def ell(x):
    return Q(3, 56) + 25*x/56


def limits(s, layer):
    if layer == 'L':
        return -min(ell(s), half-right(s)), right(s)
    u = s-half
    f = max(0, Q(17, 16)*(Q(31, 238)-u))
    g = max(0, Q(17, 16)*(Q(25, 119)-u))
    v = max(0, Q(17, 32)*(Q(19, 119)-u))
    if layer == '+':
        return right(u), half-ell(u)-max(f, v)
    return -(half-right(u)-g), -(ell(u)+v)


@dataclass(frozen=True)
class Cell:
    a: Q
    b: Q
    layer: str

    def edges(self, s):
        return limits(s, self.layer)

    def offset(self):
        return {'L': 0, '+': -half, '-': half}[self.layer]


def make_cells():
    low = [Q(0), R, half]
    upper = [half+x for x in (0, Q(12,119), Q(31,238),
                              Q(19,119), Q(25,119), R)]
    return [Cell(a,b,k) for k,knots in [('L',low),('+',upper),('-',upper)]
            for a,b in zip(knots,knots[1:])]


def projected_vertices(x, y, z):
    """Vertici del rettangolo (s_x,s_z) tagliato da 2*s_y=s_x+s_z+1."""
    lower, upper = 2*y.a-1, 2*y.b-1
    if min(x.b+z.b, upper) <= max(x.a+z.a, lower):
        return []
    candidates = list(product([x.a,x.b], [z.a,z.b]))
    candidates += [(a,h-a) for a in [x.a,x.b] for h in [lower,upper]]
    candidates += [(h-b,b) for b in [z.a,z.b] for h in [lower,upper]]
    return [(a,(a+b+1)/2,b) for a,b in set(candidates)
            if x.a <= a <= x.b and z.a <= b <= z.b and lower <= a+b <= upper]


def excludes(x,y,z,vertices,k):
    """Esclusione di t_x+t_z=2*t_y+k sull'intero dominio aperto."""
    below, above = True, True
    for sx,sy,sz in vertices:
        xl,xh = x.edges(sx)
        yl,yh = y.edges(sy)
        zl,zh = z.edges(sz)
        below &= xh+zh <= 2*yl+k
        above &= xl+zl >= 2*yh+k
    assert below or above, (x,y,z,k)


def verify():
    cells = make_cells()
    area = Q(0)
    checked_primary = checked_secondary = 0
    for cell in cells:
        l0,h0 = cell.edges(cell.a)
        l1,h1 = cell.edges(cell.b)
        assert -half <= l0 <= h0 <= half and -half <= l1 <= h1 <= half
        assert (h0-l0)+(h1-l1)>0
        assert max(abs(l1-l0),abs(h1-h0)) <= cell.b-cell.a
        if cell.layer == '+':
            assert min(l0,l1) >= 0
        if cell.layer == '-':
            assert max(h0,h1) <= 0
        area += (cell.b-cell.a)*((h0-l0)+(h1-l1))/2
    assert area == Q(579,1904)
    for x,y,z in product(cells,repeat=3):
        vertices = projected_vertices(x,y,z)
        if vertices:
            for k in (-1,0,1):
                excludes(x,y,z,vertices,k)
                checked_primary += 1
        a,b = max(x.a,y.a,z.a),min(x.b,y.b,z.b)
        if a>=b:
            continue
        multiplier = 1 if x.layer=='L' else 2
        for k in (-1,0,1):
            deficit = multiplier*k + x.offset()+z.offset()-2*y.offset()
            if deficit<0:
                excludes(x,y,z,[(a,a,a),(b,b,b)],k)
                checked_secondary += 1
    print('Area esatta:', area)
    print('Esclusioni primarie:', checked_primary)
    print('Esclusioni secondarie a s fissata:', checked_secondary)


if __name__=='__main__':
    verify()
