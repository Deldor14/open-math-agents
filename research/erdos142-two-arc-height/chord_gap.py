"""Rational upper Darboux sum for the case of a negative chord slope."""
from fractions import Fraction as Q
def pairwise(xs):
    return zip(xs,xs[1:])

def grid(lo,hi,count):
    return [lo+(hi-lo)*i/count for i in range(count+1)]

def certify(nL,ny,np):
    half=Q(1,2)
    # 13/60 is a rational upper bound for C=(10-6sqrt(2))/7.
    Cup=Q(13,60)
    assert 2*36>(10-7*Cup)**2 and 10-7*Cup>0
    answer=0
    for L0,L1 in pairwise(grid(Q(1,3),half,nL)):
        w=Q(4,7)+(2*Cup-1)/(7*L1)
        t=2-half/L0
        for y0,y1 in pairwise(grid(Q(0),half,ny)):
            value=0
            for p0,p1 in pairwise(grid(Q(0),Q(1),np)):
                first=max(0,1-p0/w)
                bound=min(Q(1,4),y1*(1-p0)+(half-y0)*first)
                if p1<=t:
                    second=max(0,1-(t-p1)/w)
                    bound=min(bound,(half-y0)*(first+second))
                value+=bound
            answer=max(answer,L1*value/np)
    assert answer==Q(178483,4194304) and answer<Q(43,1000)
    print(nL,ny,np,'boxes by coordinate; strict rational upper bound',answer,'< 43/1000.')
if __name__=='__main__':
    certify(8,16,64)
