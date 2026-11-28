"""Exact features for the endpoint tent construction in two physical coordinates."""
from fractions import Fraction as Q
from math import isqrt, lcm


def floor_surd(value):
    from verifica_parametro import Surd
    value = Surd.lift(value)
    den = lcm(value.a.denominator, value.b.denominator)
    a, b = int(value.a*den), int(value.b*den)
    r = isqrt(2*b*b)
    return (a + (r if b >= 0 else -r-1)) // den


def power(value, exponent):
    result = 1
    while exponent:
        if exponent % 2:
            result *= value
        exponent //= 2
        if exponent:
            value *= value
    return result


class TentTable:
    def __init__(self, m, mesh, trim=Q(5,8)):
        from verifica_parametro import J, V, R, G, F, q, half
        self.m, self.mesh = m, mesh
        area_inactive = J/2 - q*J*J/4
        self.trim = trim
        c = trim*q*J/(2*area_inactive)
        self.H = max(4, isqrt(floor_surd(c*m))**2)
        self.K = self.H**2
        self.tau = Q(1, self.H*isqrt(self.H))
        n = (self.K-1).bit_length()
        self.knots = [V-(V-J)/(1 << i) for i in range(n+1)]
        self.plateaus = list(zip(self.knots, self.knots[1:]))
        self.cusps = sorted(set([half, half+V] + [half+u for u in self.knots]
                               + [half+(a+b)/2 for a,b in self.plateaus]))
        self.breaks = sorted(set([0,R,half,half+G,half+F,half+R]+self.cusps))

    def geometry(self, i, j):
        from verifica_parametro import J, V, R, G, q, rr, half, Cell, Surd
        m, mesh, H, K = self.m, self.mesh, self.H, self.K
        s = Q(i, mesh)
        t = Q(j if 2*j < mesh else j-mesh, mesh)
        u = s-half
        zero = Surd(0)
        if not (0 < s < half or 0 < u < R):
            return None
        if self.knots[-1] <= u <= V:
            return None
        if any(abs(s-z) <= self.tau + Q(8,mesh) for z in self.cusps):
            return None
        if any(abs(s-z) <= Q(8,mesh) for z in self.breaks):
            return None
        sheet = 'L' if s < half else ('+' if t >= 0 else '-')
        lo, hi = Cell(None, None, sheet).edges(s)
        weight = max(zero, half-s) + max(zero, u-V)
        deformation = zero
        for a,b in self.plateaus:
            if a < u < b:
                weight = min(u-a,b-u)
                deformation = q*(u-a)
                break
        if sheet == '-':
            lo += deformation
        if sheet != 'L':
            hi += deformation/2
        e = t if sheet == 'L' else (2*t-half if sheet == '+' else 2*t+half)
        if not lo + Q(32,mesh) < t < hi - Q(32,mesh):
            return None
        if 0 < u < J:
            top = 2*rr(u) + q*(G-u)
            if e >= top - self.trim*q/H - Q(64,mesh):
                return None
        return s,t,u,e,weight,sheet

    def tick_score(self, ratio_squared):
        if ratio_squared <= 1:
            return 0
        # Write 2^(2j) <= ratio_squared^(m^2) and bisect in the integer j.
        exponent = self.m*self.m
        bits = 48+2*exponent.bit_length()
        lower = floor_surd((1 << bits)*ratio_squared)
        def dyadic_tick(numerator):
            return ((numerator**exponent).bit_length()-1-bits*exponent)//2
        lo_tick, hi_tick = dyadic_tick(lower), dyadic_tick(lower+1)
        if lo_tick==hi_tick or ratio_squared*(1 << bits)==lower:
            return lo_tick
        v = power(ratio_squared,exponent)
        high = self.m*self.m*max(1,(1+floor_surd(ratio_squared)).bit_length())
        low = 0
        while high-low > 1:
            mid = (high+low)//2
            if v >= 1 << (2*mid):
                low = mid
            else:
                high = mid
        return low

    def hinge(self,s):
        from verifica_parametro import Surd
        zero=Surd(0)
        return (8/self.tau)*sum((max(zero,s-z) for z in self.cusps),zero)

    def mark(self,s,t):
        return Q(54,100)<s<Q(55,100) and Q(12,100)<t<Q(13,100)

    def at(self,i,j):
        from verifica_parametro import V, J, half, Surd
        data = self.geometry(i,j)
        if data is None:
            return None
        s,t,u,e,weight,_ = data
        zero,K = Surd(0),self.K
        den = Q(3,2)-e
        lam = Q(15,8)
        linear = Q(59,60)-lam/3
        if u >= V:
            # Sum of length times center equals the first moment of the interval.
            comp = 2*(V-J)*(s-half-(J+V)/2)
        else:
            comp = 2*sum(((b-a)*max(zero, u-(a+b)/2) for a,b in self.plateaus), zero)
        height = K*(2*s*s-linear*s+lam*(comp+weight*weight/den))
        height += (e+half)**2+self.hinge(s)
        score = self.tick_score(K*lam*weight*weight / den**3)
        return floor_surd(self.mesh*height),score,self.mark(s,t)
