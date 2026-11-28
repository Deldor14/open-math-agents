"""Point-count the quintic Frey curve on every good slope at 3, 7, 23, 29, 47."""
from math import gcd

def traces(q, a):
    # Scale a+b to 1. All q under test have gcd(q-1,5)=1.
    b = (1-a) % q
    c3, c1, c0 = 5*a*b, 5*a*a*b*b, b**5-a**5
    squares = {i*i % q for i in range(1, q)}
    d = next(x for x in range(2,q) if x not in squares)
    def character(x):
        x %= q
        return 0 if x == 0 else 1 if x in squares else -1
    def mul(a,b):
        r,s = a
        t,u = b
        return (r*t+d*s*u) % q, (r*u+s*t) % q
    sq2 = {mul((r,s),(r,s)) for r in range(q) for s in range(q) if (r,s)!=(0,0)}
    t1 = -sum(character(x**5+c3*x**3+c1*x+c0) for x in range(q))
    t2 = 0
    for r in range(q):
        for s in range(q):
            x = (r,s)
            x2 = mul(x,x)
            x3 = mul(x2,x)
            h,k = mul(x3,x2)
            h = (h+c3*x3[0]+c1*r+c0) % q
            k = (k+c3*x3[1]+c1*s) % q
            sign = character(h*h-d*k*k)
            # Independent test of squareness in the extension by explicit enumeration.
            assert sign == (0 if (h,k)==(0,0) else 1 if (h,k) in sq2 else -1)
            t2 -= sign
    return t1,t2

def main():
    for q in (3,7,23,29,47):
        assert gcd(q-1,5)==1
        pairs = [traces(q,a) for a in range(q)]
        if q==29:
            assert pairs[0] == (0,-4*q)
            obstruction = [gcd(t1,t2+4*q) for t1,t2 in pairs]
            assert set(obstruction) == {0,2,4,6,8,12,40,160}
        else:
            assert pairs[0][1]==0 and all(t2%2==0 for _,t2 in pairs)
            obstruction = [t2//2 for _,t2 in pairs]
            if q==3: assert set(obstruction)=={0,-4}
            if q==7: assert set(obstruction)=={0,-12,-6,4}
            if q in (23,47):
                assert all(n%2==0 and abs(n)<2*59 for n in obstruction)
        assert [i for i,n in enumerate(obstruction) if n==0] == [0,1]
        print(q,'surviving slopes 0,1; obstruction values',sorted(set(obstruction)))

if __name__=='__main__':
    main()
