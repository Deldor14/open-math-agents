"""Finite row features and contiguous conditional sums for the weighted shell."""
from fractions import Fraction as Q
from itertools import accumulate
from math import isqrt,lcm
from verifica_parametro import Cell, R, Surd, V
from weights import weight_for_gap

def floor_surd(x):
    x=Surd.lift(x)
    d=lcm(x.a.denominator,x.b.denominator)
    a,b=int(x.a*d),int(x.b*d)
    r=isqrt(2*b*b)
    return (a+(r if b>=0 else -r-1))//d

def segments(start, length, q):
    """Half-open residue intervals swept by a cyclic translate."""
    start%=q
    end=start+length
    if end<=q:
        return [(start,end)]
    return [(start,q),(0,end-q)]

def sums(rows):
    return [0,*accumulate(rows)]

def add(a,b):
    return tuple(x+y for x,y in zip(a,b))

class Grid:
    def __init__(self,q,m,h):
        self.q,self.m,self.h=q,m,h
        self.H=1<<h
        self.K=self.H**2
        self.D=1 << (q*self.H).bit_length()*3
        self.scale=4*q*q*self.D**2
        self.row=[]
        self.angles={}
        self.tables={}
        half=Q(1,2)
        for sheet in ('L','+','-'):
            angle=[]
            reciprocal=[]
            for r in range(q):
                t=r if 2*r<q else r-q
                # a2 represents 2q*(1+e).
                a2=2*q+2*t if sheet=='L' else (q if sheet=='+' else 3*q)+4*t
                den=5*q-a2         # 2q*(3/2-e)
                # Outside a sheet the value is unused. The angular chart can
                # give an inadmissible denominator on these extra residues.
                inverse=(2*q*self.D)//den if den>0 else 0
                angle.append(a2*a2)
                reciprocal.append(inverse)
            self.angles[sheet]=(angle,reciprocal)
            seqs=(angle,reciprocal,[v*v for v in angle],
                  [v*x for v,x in zip(angle,reciprocal)],[x*x for x in reciprocal])
            self.tables[sheet]=tuple(sums(seq) for seq in seqs)
        eps=Q(1,128*m)
        for i in range(q):
            s=Q(i,q)
            sheets=('L',) if 0<s<half-eps else (('+','-') if half+eps<s<half+R else ())
            gap=max(Surd(0),Surd.lift(half-s))+max(Surd(0),Surd.lift(s-half)-V)
            label=weight_for_gap(gap,h)
            base=64*self.K*i*i*self.D**2+8*self.K*i*q*self.D**2
            perspective=4*q*q*self.K*floor_surd(gap*gap*self.D)
            arcs=[]
            for sheet in sheets:
                lo,hi=Cell(None,None,sheet).edges(s)
                left=floor_surd((lo+eps)*q)+1
                right=-floor_surd((eps-hi)*q)
                if right>left:
                    for a,b in segments(left,right-left,q):
                        arcs.append((a,b,sheet))
            self.row.append((label,base,perspective,arcs))
        features=[self.partial(i,0,q) for i in range(q)]
        self.rowsums=tuple(sums(col) for col in zip(*features))
        self.total=tuple(c[-1] for c in self.rowsums)

    def partial(self,i,start,length):
        """Sum (1,z,E,z²,E²) over allowed angular offsets at row i."""
        q=self.q
        label,base,p,arcs=self.row[i]
        coeff=16*self.D**2
        count=first=second=0
        for a,b in segments(start,length,q):
            for left,right,sheet in arcs:
                l,r=max(left,a),min(right,b)
                if l>=r:
                    continue
                v,u,vv,vu,uu=(c[r]-c[l] for c in self.tables[sheet])
                width=r-l
                linear=coeff*v+p*u
                count+=width
                first+=width*base+linear
                second+=width*base*base+2*base*linear+coeff*coeff*vv+2*coeff*p*vu+p*p*uu
        return count,label*count,first,label*label*count,second

    def primary(self,start,length):
        value=(0,0,0,0,0)
        for l,r in segments(start,length,self.q):
            value=add(value,tuple(c[r]-c[l] for c in self.rowsums))
        return value

    def point(self,i,t):
        label,base,p,arcs=self.row[i]
        for l,r,sheet in arcs:
            if l<=t<r:
                angles,recip=self.angles[sheet]
                return label,base+16*self.D**2*angles[t]+p*recip[t]
        return None
