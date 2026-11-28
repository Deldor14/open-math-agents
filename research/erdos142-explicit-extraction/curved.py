"""Exact local-curvature features for the larger coefficient on the same scale."""
from fractions import Fraction as Q
from tents import TentTable, floor_surd

class CurvedTable(TentTable):
    def __init__(self,m,mesh):
        super().__init__(m,mesh,trim=Q(7,16))

    def reserve(self,u):
        from verifica_parametro import J,V,Surd
        zero=Surd(0)
        if u <= J:
            return zero
        if u >= V:
            return 8*(V-J)*(u-(J+V)/2)
        total = zero
        for a,b in self.plateaus:
            if u <= a:
                break
            z = (a+b)/2
            if u >= b:
                total += 8*(b-a)*(u-z)
            else:
                total += 2*(u-a)*(u-a)+4*(b-a)*max(zero,u-z)
                break
        return total

    def at(self,i,j):
        from verifica_parametro import G,J,V,Surd,half,q,rr
        data = self.geometry(i,j)
        if data is None:
            return None
        s,t,u,e,w,sheet = data
        v = e-2*rr(u)+half
        if sheet != 'L' and v <= Q(1,self.K)+Q(64,self.mesh):
            return None
        gamma = Q(1,100)
        pos_u = max(Surd(0),Surd.lift(u))
        cap_u = max(Surd(0),u-J)
        bend = pos_u*pos_u-cap_u*cap_u
        phi = gamma*s*s+(1-gamma)*bend+Q(17,50)*s+Q(3,4)*self.reserve(u)
        angular = e*e if sheet=='L' else (v-Q(1,4))*(v-Q(1,4))
        if sheet=='L':
            lam,g,x=Q(5,8),Q(6),e-Q(1,32)
        elif u>=V:
            lam,g,x=Q(5,2),Q(7,8),e+half
        elif u>J:
            lam,g,x=Q(3,4),half,e+half
        else:
            lam,g,x=Q(0),Q(0),e
        den=1-g*x*x
        assert half <= den <= 1
        phi += lam*w*w/den
        energy = self.K*phi+angular+self.hinge(s)
        if lam:
            ratio_sq=self.K*w*w*lam*g*(lam+gamma)/(gamma*den**3)
        else:
            ratio_sq=1/gamma
        score = self.tick_score(ratio_sq)
        margin=self.tau+Q(64,self.mesh)
        if sheet=='+' and 0<u<G and margin<v<2*q*(G-u)-margin:
            score+=self.m**2
        return floor_surd(self.mesh*energy),score,self.mark(s,t)
