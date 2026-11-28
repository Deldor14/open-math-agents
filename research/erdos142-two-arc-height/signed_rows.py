"""Check the signed terminal clipping inclusions, including empty or wrapped arcs."""
from itertools import product

def clip(l,r,p,q):
    return max(0,min(r,q)-max(l,p))

def length(l,r,p,q,period):
    return r-l-sum(clip(l,r,p+k*period,q+k*period) for k in range(-3,4))

def verify(h):
    rows=[(a,z-a) for a in range(-h,2*h+1) for z in range(h+1)]
    normal=negative=0
    for (a,b),(p,q) in product(rows,repeat=2):
        A,B=a+p,b+q
        gap=(p,h-q)
        for idx,(l,r) in enumerate(((-a,b),(h-a,h+b))):
            remaining=length(l,r,*gap,2*h)
            if idx==0:
                assert remaining<=max(0,A)+max(0,B-h)
                cap=(l,min(r,p))
            else:
                assert remaining<=max(0,B)+max(0,A-h)
                cap=(max(l,h-q),r)
            if max(A,B)<=h:
                c,d=cap
                inside=length(c,d,*gap,2*h) if d>c else 0
                assert inside==remaining
        normal+=int(max(A,B)<=h)
        negative+=int(max(A,B)<=h and min(A,B)<0)
    print(len(rows)**2,'signed examples;',normal,'normal, including',negative,'with a negative cap.')
if __name__=='__main__':
    verify(8)
