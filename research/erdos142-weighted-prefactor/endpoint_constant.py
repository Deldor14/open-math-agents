"""Directed bounds for the tent construction, using the original polygon arithmetic."""
import sys
from fractions import Fraction as Q
from pathlib import Path
from mpmath import iv

sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from verifica_parametro import Surd, Cell, R, J, V, G, q, half

iv.dps = 35
pieces = int(sys.argv[2]) if len(sys.argv) > 2 else 256
assert pieces > 0
zero = Surd(0)
area = Surd(Q(17, 28), Q(-3, 14))
forced = J/2 - q*J*J/4
span = V-J


def rational(x):
    return iv.mpf(x.numerator) / x.denominator


def real(x):
    z = Surd.lift(x)
    return rational(z.a) + iv.sqrt(2)*rational(z.b)


def primitive(x, p):
    if x == 0:
        return iv.mpf(0)
    z = real(x)
    return z**(p+1)*(iv.log(z)-iv.mpf(1)/(p+1))/(p+1)


def triangle(x):
    return real(x)*primitive(x, 0)-primitive(x, 1)


def lerp(x, y, t):
    return real(x) + real(y-x)*t


y = half-R
lo = real(half)*primitive(half, 0) - real(q)*(
    primitive(half, 1)-primitive(y, 1)-real(y)*(primitive(half, 0)-primitive(y, 0)))
hi = real(q)*(2*triangle(R-V)-triangle(G-V))
pl = real(span)/2*(iv.log(real(span))-3*iv.log(2)-1)
log_tent = lo+hi+pl
mass, energy_variation, denom_integral = (iv.mpf(0) for _ in range(3))
# Interpolate the affine endpoints in the primary coordinate. On the deformed
# plateaus the total width is 1/2; all denominator and variance bounds there
# are independent of the redistribution between the two sheets.
bands = [(zero, R, 'L'), (R, Surd(half), 'L'), (half, half+J, 'B'),
         (half+J, half+V, 'P'), (half+V, half+G, 'U'), (half+G, half+R, 'U')]
lam = Q(15, 8)
drift = Q(59, 60)-lam/3
center = Q(37, 100)
for left, right, layer in bands:
    def geometry(s):
        u = s-half
        if layer == 'P':
            return Surd(half)
        if layer == 'B':
            return half-q*(J-u)/2
        sheets = ['L'] if layer == 'L' else ['+', '-']
        width = zero
        for sh in sheets:
            l, r = Cell(None, None, sh).edges(s)
            width += r-l
        return width

    wl = geometry(left)
    wr = geometry(right)
    ds = real(right-left)/pieces
    for j in range(pieces):
        t = iv.mpf([j,j+1])/pieces
        s = lerp(left,right,t)
        width = lerp(wl,wr,t)
        mass += ds*width
        if layer == 'P':
            w2 = iv.mpf([0,1])*(real(span)/4)**2
            dint = 2*width
        elif layer == 'B':
            w2 = iv.mpf(0)
            dint = iv.mpf(0)
        else:
            w2 = (real(half)-s if layer == 'L' else s-real(half+V))**2
            dint = iv.mpf(0)
            for sh in (['L'] if layer == 'L' else ['+', '-']):
                l0,r0 = Cell(None,None,sh).edges(left)
                l1,r1 = Cell(None,None,sh).edges(right)
                # Physical integral of D=3/2-e in that angular interval.
                p, off = {'L':(1,0), '+':(2,-half), '-':(2,half)}[sh]
                w = lerp(r0-l0,r1-l1,t)
                mid = lerp((l0+r0)/2,(l1+r1)/2,t)
                dint += w*(real(Q(3,2)-off)-p*mid)
        # Bracket the full infinite hinge sum by its two extreme centers.
        h0 = lerp(max(zero,left-half-V),max(zero,right-half-V),t)
        h1 = lerp(max(zero,left-half-J),max(zero,right-half-J),t)
        hinge = 2*real(span)*iv.mpf([h0.a,h1.b])
        phi = 2*s**2-real(drift)*s+real(lam)*(hinge+w2*iv.mpf(['0.5','1']))
        energy_variation += ds*width*(phi-real(center))**2
        denom_integral += ds*dint

A = real(area)
rho = real(forced)/A
theta = 1-rho
beta = theta/2-iv.mpf(1)/4
a = iv.log(1/A)
c = real(5*q*J/(16*forced))
# Jensen's inequality for log D on the active part, using its first moment.
mean_d_upper = denom_integral.b/(A*theta)
mu_lower = iv.log(4*iv.sqrt(2))+theta*iv.log(real(lam))/2+log_tent/A-iv.mpf('1.5')*theta*iv.log(mean_d_upper)
sigma_upper = iv.sqrt(energy_variation.b/A)
coefficient = (a**(-beta)*iv.exp(mu_lower-rho)*c**(-rho) /
               (iv.sqrt(A)*4*iv.pi*iv.exp(1)*iv.sqrt(2*iv.pi)*sigma_upper))
assert mass.a <= A.a and A.b <= mass.b
print('certified lower comparison:', coefficient)
print('sigma upper:', sigma_upper, 'mean D upper:', mean_d_upper)
print('log tent integral:', log_tent)

if pieces == 256:
    assert coefficient.a > rational(Q(244079, 10_000_000)).b
