"""Exact profile alignments and integer tent coefficients at a signed benchmark."""
from fractions import Fraction as F
from check_signed_endpoint import intervals, p, q

half = F(1, 2)
quarter = F(1, 4)


def check(m):
    t0, step = F(1,16), F(1,64*m)
    margin = (p+q)*step/16
    e = 2*margin
    rows = {}
    for i in range(-m, m+1):
        t = t0+i*step
        pos, neg = intervals(half+t)
        left, high = pos[0]-half, pos[1]-half
        low, right = neg[:2]
        assert left < low < high < right
        v = right-e-quarter
        assert low+margin < v < high-margin
        assert left+e < v < right-e and left+e < high-e < right-e
        assert high-e > left+margin and right-e > low+margin
        assert 2*(right-e) == (v+half)+v
        rows[i] = left+e, high-e, right-e
    for i in range(-m+1, m):
        ypos, xpos, zneg = rows[i][0]+half, rows[i+1][1]+half, rows[i-1][2]
        assert xpos+zneg == 2*ypos
    def w(i):
        return max(0, m-abs(i))
    grid = range(-m-1,m+2)
    assert sum(w(i) for i in grid) == m*m
    first = sum(max(abs(w(i-1)-w(i))-F(w(i),2),0) for i in grid)
    second = sum(max(w(i-1)+w(i+1)-2*w(i),0) for i in grid)
    assert first <= 3 and second == 2
    print(f'm={m}: {2*m-1} moving progressions, tent mass={m*m}, dual costs={first},{second}')


if __name__ == '__main__':
    for m in (2, 3, 8, 64, 128, 256):
        check(m)
