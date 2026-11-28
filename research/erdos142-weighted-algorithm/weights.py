"""A single exact product kernel dominates all typical angular profiles."""
from fractions import Fraction as Q
from math import isqrt
from scores import powers_of_generator, product_scores

def ceil_sqrt(m):
    return isqrt(m-1)+1

def angular_types(h):
    """(dyadic angular weight, probability, log2(weight*probability))."""
    yield 1,Q(1,2),-1
    for j in range(h):
        yield 1 << (h-j), Q(1,1 << (j+2)), h-2*j-2
    yield 1,Q(1,1 << (h+1)),-h-1

def weight_for_gap(a,h):
    if a == 0:
        return -1
    j=0
    while j<h and (1<<j)*a<1:
        j+=1
    return h-2*j-2 if j<h else -h-1

def kernels(q,m,h,u):
    """The returned arrays, divided by scale, majorize the product factors."""
    H=1<<h
    dyad=1 << (q*H).bit_length()
    mult=1 << (h+1)
    scale=dyad*mult
    def response(weight):
        c=u.numerator*q*q
        e=m*u.denominator*weight**2
        out=[]
        for i in range(q):
            den=c+e*min(i,q-i)**2
            out.append((c*dyad+den-1)//den)
        return out
    primary=[mult*x for x in response(H)]
    angular=[0]*q
    for weight,prob,_ in angular_types(h):
        coef=int(mult*prob)*weight
        for i,x in enumerate(response(weight)):
            angular[i]+=coef*x
    return primary,angular,scale

def certificate(n,q,m,h,ell):
    # The asymptotic proof guarantees success before u falls below 1/q².
    # For small grids the caller has a separate positive separation bound.
    u=Q(m*(1<<h)**2)
    while u>=Q(1,q*q):
        first,second,scale=kernels(q,m,h,u)
        den=(q*scale)**(2*m)
        lhs=(n-1)*(4*sum(first)*sum(second))**m
        if lhs*(1<<max(0,-ell)) < den*(1<<max(0,ell)):
            return u,first,second
        u/=2
    return None

def select_direction(n,m,q,primary,secondary):
    powers=powers_of_generator(q)
    products=[1]*(n-1)
    coords=[]
    for kernel in (primary,secondary)*m:
        scores=product_scores(products,kernel,powers)
        k=min(range(q),key=scores.__getitem__)
        for d in range(1,n):
            products[d-1]*=kernel[d*k%q]
        coords.append(k)
    return list(zip(coords[::2],coords[1::2]))

def unconditional_separation(vectors,q,n,H):
    return min(Q(sum(H*H*min(d*s%q,(-d*s)%q)**2+min(d*t%q,(-d*t)%q)**2
                     for s,t in vectors),q*q) for d in range(1,n))
