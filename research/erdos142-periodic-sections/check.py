"""Independent small certificate, using literal line segments of the parity body."""
from fractions import Fraction as F

def width(q,n,low):
    h=n//2
    rectangles=((0,h,0,n),(h,n,0,h)) if low else ((0,h,0,h),)
    return sum(max(0,min(b,q-c)-max(a,q-d)) for a,b,c,d in rectangles)

def check(n,cap):
    # All slope changes of these segment lengths are integer multiples of n/2.
    envelope={(k,low):min(cap,max(width(k+d,n,low) for d in (-1,0,1)))
              for k in range(1-n,2*n) for low in (True,False)}
    a=F(304098,10**6); answer=0
    for i in range(2*n):
        w=[envelope[i-j,j<n//2] for j in range(n)]
        overlap=max(sum(min(w[j],max(w[(j+r)%n],w[(j+r+1)%n])) for j in range(n))
                    for r in range(n//3,n//2+1))
        answer+=min(a,F(sum(w),n*n),(a+F(overlap,n*n))/2)
    return answer/(2*n)

if __name__=='__main__':
    n=180
    result=check(n,n)
    assert result==F(152677547,911250000)
    refined=check(n,n//2)
    assert refined==F(3883841350400,23328000000000)
    a_lo,a_hi=F(304097,10**6),F(304098,10**6)
    assert (17-28*a_hi)**2<72<(17-28*a_lo)**2 and 17>28*a_hi
    lower=F(167694,10**6)
    assert lower**2<a_lo**3 and result<lower
    sharp=F(1146989681440000,6912000000000000)
    assert 4*(lower-sharp)>F(7,1000)
    print('Mesh 180, unrestricted and circle cap:',result,refined)
    print('Threshold >',lower,'; mean symmetric difference needed > 7/1000 at mesh 1200')
