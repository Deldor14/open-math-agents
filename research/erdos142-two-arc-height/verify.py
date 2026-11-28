"""Check the four cases and both boundary witnesses on a rational endpoint grid."""
from fractions import Fraction as Q
from itertools import combinations,product
from collections import Counter

def arc_t(e,side):
    return (e+Q(side,2))/2

def run(n):
    points=[Q(i,n)-Q(1,2) for i in range(n+1)]
    pairs=list(combinations(points,2)); counts=Counter()
    for (l,r),(p,d) in product(pairs,repeat=2):
        # Coordinates e reflect the actual signs of physical t.
        A,B=min(l,p),max(r,d)
        M0,M1=(l+p)/2,(r+d)/2
        four=(r+d-2*A<=1,2*B-l-p<=1,r<=p,d<=l)
        # The exact four inequalities in CubeJerry's signed widths.
        P,V,U,M=2*r,-2*l,2*d,-2*p
        assert four==(P+U+2*max(V,M)<=2,V+M+2*max(P,U)<=2,
                      P+M<=0,U+V<=0)
        if any(four):
            counts['admissible']+=1
            if four[2]:
                assert arc_t(r,1)-arc_t(p,-1)<=Q(1,2)
            if four[3]:
                assert 1+arc_t(d,-1)-arc_t(l,1)<=Q(1,2)
            continue
        counts['flat']+=1
        assert max(l,p)<min(r,d)
        for edge,offset in ((A,Q(1,2)),(B,-Q(1,2))):
            mean=edge+offset
            assert M0<mean<M1
            alpha=(mean-M0)/(M1-M0)
            x,z=l+alpha*(r-l),p+alpha*(d-p)
            assert l<x<r and p<z<d and (x+z)/2==mean
            step=min(x-l,r-x,z-p,d-z,B-A)/8
            # Make an actual open-arc midpoint arbitrarily near the edge.
            for lo,hi in ((l,r),(p,d)):
                if lo==A or hi==B:
                    step=min(step,(hi-lo)/8)
            eps=step if edge==A else -step
            y=edge+eps
            signs=[sg for sg,(left,right) in [(1,(l,r)),(-1,(p,d))] if left<y<right]
            assert signs
            for sg in signs:
                res=arc_t(x+eps,1)+arc_t(z+eps,-1)-2*arc_t(y,sg)
                assert res.denominator==1
    print(n,len(pairs)**2,dict(counts))
    return counts
if __name__=='__main__':
    for n in (8,12,16):run(n)
