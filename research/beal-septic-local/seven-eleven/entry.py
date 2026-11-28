"""Direct denominator-cleared congruences in Z[zeta_7]/121 for the signature (7,7,11)."""
m=121
one=(1,0,0,0,0,0,0); z=(0,1,0,0,0,0,0); zp=(0,0,0,0,1,0,0)

def add(a,b):return tuple((x+y)%m for x,y in zip(a,b))

def scale(a,n):return tuple(x*n%m for x in a)

def mul(a,b):return tuple(sum(a[j]*b[(i-j)%7] for j in range(7))%m for i in range(7))

def power(a,n):
    result=one
    while n:
        if n%2:result=mul(result,a)
        a=mul(a,a);n//=2
    return result

def equal(a,b):return len({(x-y)%m for x,y in zip(a,b)})==1

slopes=[]
for t in range(121):
    if (1+t)%11==0:continue
    A=add(scale(one,t),z);sA=add(scale(one,t),zp)
    if equal(scale(power(A,11),t+1),scale(sA,pow(t+1,11,121))):slopes.append(t)
# If 11|D, t=-1 mod 121, and A^6/Q must reduce to (z-1)^6/7.
E=scale(power(add(z,scale(one,-1)),6),pow(7,-1,121));sE=scale(power(add(zp,scale(one,-1)),6),pow(7,-1,121))
assert slopes==[0] and not equal(power(E,11),sE)
print('finite slopes with 11 not dividing D:',slopes,'exceptional slope -1 excluded')
