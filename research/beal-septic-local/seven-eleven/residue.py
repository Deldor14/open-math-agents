"""Exact residue and determinant checks for the lambda-descent, in the theta basis."""


def product(a,b,m):
    c=[0]*5
    for i,u in enumerate(a):
        for j,v in enumerate(b): c[i+j]+=u*v
    for k in [4,3]:
        t=c[k]
        c[k-1]-=t;c[k-2]+=2*t;c[k-3]+=t
    return tuple(x%m for x in c[:3])


def power(a,k,m):
    out=(1,0,0)
    while k:
        if k%2:out=product(out,a,m)
        a=product(a,a,m);k//=2
    return out


def plus(a,b,m):return tuple((x+y)%m for x,y in zip(a,b))


def times(n,a,m):return tuple(n*x%m for x in a)


def determinant(columns):
    a,b,c=columns
    return (a[0]*(b[1]*c[2]-b[2]*c[1])-b[0]*(a[1]*c[2]-a[2]*c[1])+c[0]*(a[1]*b[2]-a[2]*b[1]))%11


def main():
    assert all((x**3+x**2-2*x-1)%11 for x in range(11))
    # In O_K/121 the unit group exponent divides 11*(11^3-1).
    m=121; one=(1,0,0); th=(0,1,0)
    u=product(plus(th,one,m),plus(th,(2,0,0),m),m)
    target=times(-1,power(times(4,u,m),11*1330-1,m),m)
    root=power(target,121,m)
    w=plus(one,product(times(4,u,m),power(root,11,m),m),m)
    assert all(v%11==0 for v in w)
    lead=tuple((-v//11)%11 for v in w)
    assert power(lead,665,11)==(10,0,0)
    real=[th,(-2,0,1),(1,-1,-1)]
    H=[power(plus((2,0,0),times(-1,b,11),11),1329,11) for b in real]
    J=[plus(h,times(-6,product(h,h,11),11),11) for h in H]
    assert determinant(H)==determinant(J)==5
    print('numerator mod 121:',w,'nonsquare leading coefficient:',lead,'minors:',determinant(H),determinant(J))


def high_grades():
    from math import factorial
    th=(0,1,0); zero=(0,0,0);one=(1,0,0)
    conjugates=[th,(-2,0,1),(1,-1,-1)]
    hlist=[power(plus((2,0,0),times(-1,t,11),11),1329,11) for t in conjugates]
    def coefficients(h):
        f=[zero]+[times(2*pow(factorial(2*j),-1,11),h,11) for j in range(1,5)]
        term=[one]+[zero]*4;out=[zero]*5
        for k in range(1,5):
            term=[sumring([product(term[i],f[j-i],11) for i in range(j+1)]) for j in range(5)]
            out=[plus(a,times((-1)**(k-1)*pow(k,-1,11),v,11),11) for a,v in zip(out,term)]
        return out[1:]
    def sumring(items):
        out=zero
        for a in items:out=plus(out,a,11)
        return out
    dets=[determinant(cs) for cs in zip(*(coefficients(h) for h in hlist))]
    top=[]
    for t in conjugates[:2]:
        y=power(t,1330,121)
        top.append(tuple((a-(i==0))//11 for i,a in enumerate(y)))
    print('graded minors',dets,'unramified-unit columns',top)
    assert all(dets) and any((top[0][i]*top[1][j]-top[0][j]*top[1][i])%11 for i in range(3) for j in range(i))


if __name__=='__main__':
    main()
    high_grades()
