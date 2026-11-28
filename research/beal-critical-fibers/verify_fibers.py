"""Exhaustive sample of the complete smooth/critical lifting rule for a+b=1."""
from math import isqrt


def prime(p):
    return p>=2 and all(p%q for q in range(2,isqrt(p)+1))


def verify():
    tested=regular=critical=0
    for p in range(11,200):
        if not prime(p):continue
        m=p*p
        # A p-th power mod p² is the p-th power of a representative
        # mod p, since (x+p*t)^p=x^p mod p².
        image={pow(x,p,m) for x in range(p)}
        for k in (5,7):
            for x in range(p):
                value=(pow(x,k,m)+pow(1-x,k,m))%m
                deriv=k*(pow(x,k-1,p)-pow(1-x,k-1,p))%p
                lifts=[j for j in range(p) if
                    (pow(x+j*p,k,m)+pow(1-x-j*p,k,m))%m in image]
                tested+=1
                if deriv:
                    delta=(pow(value,p,m)-value)%m
                    assert delta%p==0
                    assert lifts==[(delta//p)*pow(deriv,-1,p)%p]
                    regular+=1
                else:
                    b=1-x
                    if (x-b)%p==0:base=2
                    elif k==5 and (x*x+b*b)%p==0:base=2
                    elif k==7 and (x*x-x*b+b*b)%p==0:base=3
                    else:
                        assert k==7 and (x*x+x*b+b*b)%p==0
                        base=1
                    allowed=pow(base,p-1,m)==1
                    assert lifts==(list(range(p)) if allowed else [])
                    critical+=1
    print('Residue classes:',tested,'regular:',regular,'critical:',critical)


if __name__=='__main__':verify()
