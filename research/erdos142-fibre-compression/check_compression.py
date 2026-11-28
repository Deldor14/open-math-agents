"""Exhaust every pair of open unions of equal grid cells, at each mesh 1 through 9."""
from itertools import product

def run(k):
    # A unit cell j is (j,j+1); the positive half-circle is (0,k), period 2k.
    cells=[tuple(j for j in range(k) if (mask>>j)&1) for mask in range(1<<k)]
    support=[sum(1<<j for j in c) for c in cells]
    def meets(x,y,z):
        return x<z+1 and z<y
    def make_allowed(X,Y):
        for x in X:
            for y in Y:
                for z in Y:
                    if meets(x+2*y,x+2*y+3,z):return False
                for z in X:
                    if meets(y+2*x,y+2*x+3,2*k+z):return False
        return True
    # For a fixed middle Y-cell, mark which positive X-cells can meet a target in Y.
    bad_y=[]
    for Y in cells:
        bad_y.append(sum(1<<x for x in range(k)
                     if any(meets(x+2*y,x+2*y+3,z) for y in Y for z in Y)))
    bad_x=[]
    for X in cells:
        bad_x.append(sum(1<<y for y in range(k)
                     if any(meets(y+2*x,y+2*x+3,2*k+z) for x in X for z in X)))
    total=disconnected=0
    for i,X in enumerate(cells):
        for j,Y in enumerate(cells):
            good=not (i&bad_y[j] or j&bad_x[i])
            if k<=5:assert good==make_allowed(X,Y)
            if not good:continue
            total+=1
            size=len(X)+len(Y)
            if not X or not Y:continue
            p,P,n,M=X[0],X[-1]+1,Y[0],Y[-1]+1
            disconnected+=len(X)<P-p or len(Y)<M-n
            if P+2*n<=M:
                assert size<=M-n
            elif n+2*P-2*k>=p:
                assert size<=P-p
            else:
                # Scale the endpoints by two to preserve half-grid cuts.
                rhs=min(2*P,2*k-M+p);lhs=max(2*n,M-p)
                assert 2*p<=rhs and lhs<=2*M
                assert rhs-2*p+2*M-lhs>=2*size
                assert 2*M<=2*p+2*lhs and 2*M+2*rhs<=4*k+2*p
    return total,disconnected
if __name__=='__main__':
    for k in range(1,10):
        print(k,4**k,*run(k))
