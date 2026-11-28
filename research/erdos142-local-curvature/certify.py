"""Directed lower comparison for local curvature reserves on the plateau construction."""
from fractions import Fraction as Q
from pathlib import Path
import sys
from mpmath import iv

sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from verifica_parametro import Surd, Cell, R, J, V, G, q as b, half

iv.dps = 32
n = int(sys.argv[2]) if len(sys.argv)>2 else 96
assert n > 0
zero = Surd(0)
A = Surd(Q(17,28), Q(-3,14))
bad = J/2-b*J*J/4
span = V-J
gamma = Q(1,100)
drift = Q(-17,50)
plateau_lambda = Q(3,4)
center = Q(23,100)

def rat(x):
    return iv.mpf(x.numerator)/x.denominator

def real(x):
    x = Surd.lift(x)
    return rat(x.a)+iv.sqrt(2)*rat(x.b)

def log_integral(x, k):
    if x == 0:
        return iv.mpf(0)
    y = real(x)
    return y**(k+1)*(iv.log(y)-iv.mpf(1)/(k+1))/(k+1)

# Physical area divided by du is affine on each piece. Changing variables to
# the tent height gives this integral on both exterior components.
def exterior_log(a0, a1, w0, w1):
    slope = (w1-w0)/(a1-a0)
    intercept = w0-slope*a0
    left,right = sorted((a0,a1))
    return sum(real(c)*(log_integral(right,k)-log_integral(left,k))
               for k,c in enumerate((intercept,slope)))

log_volume = real(span)/2*(iv.log(real(span))-3*iv.log(2)-1)
energy_square = iv.mpf(0)
total_mass = zero
bands = [(zero,R,'L'), (R,Surd(half),'L'), (half,half+J,'B'),
         (half+J,half+V,'P'), (half+V,half+G,'U'), (half+G,half+R,'U')]

for left,right,kind in bands:
    angle_parts = ['L'] if kind=='L' else ['+','-'] if kind=='U' else ['whole']
    for part in angle_parts:
        def geometry(s):
            u = s-half
            if kind=='P':
                return Surd(half),zero,zero
            if kind=='B':
                return half-b*(J-u)/2,zero,zero
            lo,hi = Cell(None,None,part).edges(s)
            shift = {'L':Q(-1,32), '+':0, '-':1}[part]
            p = 1 if part=='L' else 2
            return hi-lo,p*lo+shift,p*hi+shift

        w0,l0,h0 = geometry(left)
        w1,l1,h1 = geometry(right)
        total_mass += (right-left)*(w0+w1)/2
        if kind=='L':
            lam,g = Q(5,8),Q(6)
            a0,a1 = half-left,half-right
        elif kind=='U':
            lam,g = Q(5,2),Q(7,8)
            a0,a1 = left-half-V,right-half-V
        elif kind=='P':
            lam,g = plateau_lambda,Q(1,2)
        if kind in ('L','U'):
            log_volume += exterior_log(a0,a1,w0,w1)
            for s,v in ((left,l0),(left,h0),(right,l1),(right,h1)):
                assert 1-g*v*v >= half
                if kind=='L':
                    assert 2*(half-s)*(half-s) <= Q(55,100)*(1-g*v*v)
        if kind != 'B':
            mass = real((right-left)*(w0+w1)/2)
            log_volume += mass*iv.log(rat(lam*g*(lam+gamma)))/2
        for i in range(n):
            t = iv.mpf([i,i+1])/n
            s = real(left)+real(right-left)*t
            w = real(w0)+real(w1-w0)*t
            ds = real(right-left)/n
            if kind=='L':
                bend = padding = 0
            elif kind=='B':
                bend = (s-real(half))**2
                padding = 0
            else:
                bend = 2*real(J)*(s-real(half))-real(J)**2
                if kind=='U':
                    padding = 8*real(span)*(s-real(half+(J+V)/2))
                else:
                    padding = iv.mpf([0,1])*4*(s-real(half+J))**2
            phi = rat(gamma)*s**2+(1-rat(gamma))*bend-rat(drift)*s+rat(plateau_lambda)*padding
            if kind in ('L','U'):
                v0 = real(l0)+real(l1-l0)*t
                v1 = real(h0)+real(h1-h0)*t
                tent = real(a0)+real(a1-a0)*t
                # Integrate over a unit affine angular parameter; its physical
                # Jacobian on the sheet is the physical width w.
                for j in range(8):
                    v = v0+(v1-v0)*iv.mpf([j,j+1])/8
                    den = 1-rat(g)*v**2
                    energy_square += ds*w/8*(phi+rat(lam)*tent**2/den-rat(center))**2
                    log_volume -= 3*ds*w/16*iv.log(den)
            else:
                if kind=='P':
                    phi += rat(lam)*iv.mpf([0,2])*(real(span)/4)**2
                energy_square += ds*w*(phi-rat(center))**2

area = real(A)
assert total_mass == A
assert gamma/2-drift-Q(55,100)*Q(5,8)==Q(1,800)
assert 4*b*G*(1-b*G)<Q(49,64) and b*G<half
rho = real(bad)/area
beta = iv.mpf(1)/4-rho/2
kappa = real(7*b*J/32)
scale = kappa/real(bad)
sigma = iv.sqrt(energy_square.b/area)
# For 0<u<G an e-strip of length 2g(u) on the positive sheet has
# exactly one available middle lift. The physical area is integral g.
single = b*G*G/2
assert G > (J+V)/2 and G > V/2
mu = iv.log(4)+real(single)/area*iv.log(2)+log_volume/area
coefficient = (iv.log(1/area)**(-beta)*iv.exp(mu-rho)*scale**(-rho)/
               (iv.sqrt(area)*4*iv.pi*iv.exp(1)*iv.sqrt(2*iv.pi)*sigma))
print('sigma upper',sigma,'mu lower comparison',mu.a,'coefficient lower comparison',coefficient.a)

if n == 256:
    assert coefficient.a > rat(Q(127,1000)).b
