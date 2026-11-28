"""Independent exhaustive small-grid checks for each part of the construction."""
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import json
import sys
from construct import construct,translate
from features import Grid,floor_surd
from weights import angular_types,kernels,select_direction
from verifica_parametro import Cell,Surd,R,V

def direct_point(grid,i,t):
    q,m,H,D=grid.q,grid.m,grid.H,grid.D
    s=Q(i,q)
    y=Q(t if 2*t<q else t-q,q)
    eps=Q(1,128*m)
    possible=('L',) if 0<s<Q(1,2)-eps else ('+','-') if Q(1,2)+eps<s<Q(1,2)+R else ()
    for layer in possible:
        lo,hi=Cell(None,None,layer).edges(s)
        if not lo+eps<y<hi-eps:continue
        g=max(0,Q(1,2)-s)+max(Surd(0),s-Q(1,2)-V)
        e=y if layer=='L' else 2*y+(-Q(1,2) if layer=='+' else Q(1,2))
        z=-1
        if g>0:
            j=next((j for j in range(grid.h) if 2**j*g>=1),grid.h)
            z=grid.h-2*j-2 if j<grid.h else -grid.h-1
        height=16*(H**2*s*s+(1+e)**2)+H**2*(g*g/(Q(3,2)-e)+2*s)
        lower=16*(H**2*s*s+(1+e)**2)+H**2*(Q(floor_surd(D*g*g),D)*Q(D//(Q(3,2)-e),D)+2*s)
        assert 0<=height-lower<=Q(2*H**2,D)
        val=lower*grid.scale
        assert val.denominator==1
        return z,int(val),height,g
    return None

def sums(values):
    return tuple(sum(x) for x in zip(*[(1,z,e,z*z,e*e) for z,e in values])) if values else (0,0,0,0,0)

def check_grid(q,m):
    g=Grid(q,m,(1024*m-1).bit_length())
    points={}
    for i,t in product(range(q),repeat=2):
        v=direct_point(g,i,t)
        if v:points[i,t]=v
        assert g.point(i,t)==(v[:2] if v else None)
    for row,start,length in product(range(q),range(q),(1,2,q//2,q)):
        eligible=[points[row,t][:2] for k in range(length) if (row,(t:=(start+k)%q)) in points]
        assert sums(eligible)==g.partial(row,start,length)
    n=q-2
    vectors=[((3+i)%q,(1+2*i)%q) for i in range(m)]
    shifts,matching=translate(n,g,vectors)
    replay={}
    for x in range(1,n+1):
        chain=[points.get(((x*d+b)%q,(x*t*((q+1)//2)+c)%q)) for (d,t),(b,c) in zip(vectors,shifts)]
        if all(a is not None for a in chain):
            replay[x]=tuple(sum(a[k] for a in chain) for k in (0,1))
    assert replay==matching
    M,Z,E,ZZ,EE=g.total
    Bz=64*m*(M*(g.h+2))**2
    Be=64*m*(M*64*g.K*g.scale)**2
    end=sum(Bz*Be-Be*(M*z-m*Z)**2-Bz*(M*e-m*E)**2 for z,e in replay.values())
    initial=Bz*Be-Be*m*(M*ZZ-Z*Z)-Bz*m*(M*EE-E*E)
    assert end*q**(2*m)>=n*M**m*initial
    triples=0
    if q<=19:
        for x,z in combinations(points,2):
            y=tuple(((a+b)*((q+1)//2))%q for a,b in zip(x,z))
            if y not in points:continue
            ds=Q(x[0]-z[0],q)
            dt=(2*(x[1]-z[1]))%q
            ang=Q(min(dt,q-dt),q)
            gap=points[x][3]
            loss=points[x][2]+points[z][2]-2*points[y][2]
            assert 256*loss>=g.K*ds**2+ang**2+g.K*gap*gap*ang**2
            triples+=1
    return len(points),triples

def check_mixture():
    q,h,m=11,3,2
    u=Q(5,3)
    first,second,scale=kernels(q,m,h,u)
    types=list(angular_types(h))
    assert sum(p for _,p,_ in types)==1
    H=2**h
    cases=0
    for rs in product(range(3),repeat=4):
        proxy=Q(first[rs[0]]*second[rs[1]]*first[rs[2]]*second[rs[3]],scale**4)
        for (l1,p1,z1),(l2,p2,z2) in product(types,repeat=2):
            terms=[Q((w*x)**2,q*q) for w,x in zip((H,l1,H,l2),rs)]
            selected=p1*l1*p2*l2
            for e in terms:selected/=1+m*e/u
            assert proxy>=selected
            if sum(terms)<=u:
                assert proxy>Q(2)**(z1+z2)/4**m
                cases+=1
    vectors=select_direction(6,m,q,first,second)
    prod_so_far=[1]*5
    for c,w in zip(sum((list(x) for x in vectors),[]),(first,second)*m):
        direct=[sum(prod_so_far[d-1]*w[d*a%q] for d in range(1,6)) for a in range(q)]
        assert direct[c]==min(direct)
        prod_so_far=[x*w[d*c%q] for d,x in enumerate(prod_so_far,1)]
    return cases

if __name__=='__main__':
    print('Weighted grid points and nonconstant midpoint triples:',[check_grid(q,m) for q,m in ((13,1),(17,2),(19,2),(31,3))])
    print('Small-metric labelled tuples:',check_mixture())
    examples=Path(__file__).with_name('examples.json')
    if examples.exists():
        for record in json.loads(examples.read_text()):
            source=set(record['sites'])
            assert source and min(source)>=1 and max(source)<=record['N']
            assert all(2*y-x not in source for x,y in combinations(sorted(source),2))
            assert json.loads(json.dumps(construct(record['N'],record['m'],record['q'])))==record
        print('Saved examples reproduced.')
