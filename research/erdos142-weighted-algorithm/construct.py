"""Construct a three-progression-free subset by a deterministic weighted shell."""
import argparse
import json
from fractions import Fraction as Q
from math import isqrt
from features import Grid
from verifica_parametro import Surd
from weights import certificate, ceil_sqrt, select_direction, unconditional_separation

def first_prime(n):
    end=2*max(n,3)
    sieve=bytearray([1])*(end+1)
    for i in range(2,isqrt(end)+1):
        if sieve[i]:
            sieve[i*i::i]=bytes((end-i*i)//i+1)
    return next(v for v in range(max(n+1,3),end+1) if sieve[v])

def choose_dimension(n):
    area=Surd(Q(17,28),-Q(3,14))
    best=Surd(0)
    power=Surd(1)
    winner=1
    for m in range(1,n.bit_length()+1):
        power=power*area*area
        lo,hi=0,1
        while hi**(2*m)<n:
            hi*=2
        while hi-lo>1:
            mid=(hi+lo)//2
            if mid**(2*m)<n:
                lo=mid
            else:
                hi=mid
        score=power/(m*hi**4)
        if score>best:
            winner,best=m,score
    return winner

def choose_half(q,evaluate):
    left,right=0,q
    while right-left>1:
        mid=(left+right)//2
        a=evaluate(left,mid-left)
        b=evaluate(mid,right-mid)
        if a*(right-mid)>=b*(mid-left):
            right=mid
        else:
            left=mid
    return left

def translate(n,grid,vectors):
    size,z_sum,e_sum,z2,e2=grid.total
    m,q=grid.m,grid.q
    z_budget=64*m*(size*(grid.h+2))**2
    e_budget=64*m*(size*64*grid.K*grid.scale)**2
    z_variance=size*z2-z_sum*z_sum
    e_variance=size*e2-e_sum*e_sum
    states={x:(0,0) for x in range(1,n+1)}
    shifts=[]
    for j,(d,beta) in enumerate(vectors,1):
        step=beta*((q+1)//2)%q
        points=[(x,x*d%q,x*step%q,sz,se) for x,(sz,se) in states.items()]
        remaining=m-j
        def score(stats,sz,se):
            c,z,e,zz,ee=stats
            az,ae=sz-z_sum,se-e_sum
            zz_term=c*(az*az+remaining*z_variance)+2*az*size*z+size*size*zz
            ee_term=c*(ae*ae+remaining*e_variance)+2*ae*size*e+size*size*ee
            return c*z_budget*e_budget-e_budget*zz_term-z_budget*ee_term
        def primary(left,length):
            return sum(score(grid.primary(s+left,length),sz,se) for _,s,_,sz,se in points)
        hs=choose_half(q,primary)
        def angular(left,length):
            return sum(score(grid.partial((s+hs)%q,t+left,length),sz,se) for _,s,t,sz,se in points)
        ht=choose_half(q,angular)
        shifts.append((hs,ht))
        states={}
        for x,s,t,sz,se in points:
            features=grid.point((s+hs)%q,(t+ht)%q)
            if features is not None:
                z,e=features
                states[x]=(sz+size*z-z_sum,se+size*e-e_sum)
    return shifts,{x:((sz+m*z_sum)//size,(se+m*e_sum)//size) for x,(sz,se) in states.items()}

def extract(points,width,scale,ell):
    sorted_sites=sorted((energy,x) for x,(label,energy) in points.items() if label>=ell)
    if not sorted_sites:return []
    lo=0
    best_lo=best_hi=0
    for hi,(energy,_) in enumerate(sorted_sites):
        while (energy-sorted_sites[lo][0])*width.denominator>=width.numerator*scale:
            lo+=1
        if hi+1-lo>best_hi-best_lo:
            best_lo,best_hi=lo,hi+1
    return sorted(x for _,x in sorted_sites[best_lo:best_hi])

def construct(n,m=None,q=None):
    if n<2:raise ValueError('N must be at least two')
    m=choose_dimension(n) if m is None else m
    if m<=0:raise ValueError('m must be positive')
    q=first_prime(n) if q is None else q
    if q<=n or q<3 or any(q%d==0 for d in range(2,isqrt(q)+1)):
        raise ValueError('q must be an odd prime greater than N')
    h=(1024*m-1).bit_length()
    grid=Grid(q,m,h)
    size,z_sum,*_=grid.total
    if not size:return {'N':n,'m':m,'q':q,'method':'empty-grid singleton','sites':[1]}
    min_label=min(label for label,_,_,arcs in grid.row if arcs)
    ell=max(m*min_label,m*z_sum//size-8*(h+2)*ceil_sqrt(m))
    cert=certificate(n,q,m,h,ell)
    if cert is None:
        vectors=[(1,1)]*m
        u=unconditional_separation(vectors,q,n,grid.H)
        method='small-grid unconditional separation'
    else:
        u,first,second=cert
        vectors=select_direction(n,m,q,first,second)
        u=max(u,unconditional_separation(vectors,q,n,grid.H))
        method='weighted mixture certificate'
    width=u/2048
    if Q(4*m*grid.K,grid.D)>width:
        return {'N':n,'m':m,'q':q,'method':'small-grid rounding singleton','sites':[1]}
    shifts,points=translate(n,grid,vectors)
    sites=extract(points,width,grid.scale,ell)
    return {'N':n,'m':m,'q':q,'method':method,'direction_primary_and_doubled_angular':vectors,
            'shifts':shifts,'minimum_score':ell,'metric_threshold':[u.numerator,u.denominator],
            'grid_eligible_sites':sum(z>=ell for z,e in points.values()),'sites':sites}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('N',type=int)
    parser.add_argument('--dimension',type=int)
    parser.add_argument('--prime',type=int)
    args=parser.parse_args()
    print(json.dumps(construct(args.N,args.dimension,args.prime)))
