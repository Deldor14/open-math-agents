"""Exact mesh labels for the two-level perspective energy on the frozen 3D clip."""
import argparse
from fractions import Fraction as F
from itertools import product
from math import isqrt
from block import Block
from finite import alphabet,extract


def cell_distance(x,resolution):
    a=(x*resolution)%1
    return min(a,1-a)/resolution


def nested(x,w,g):
    return x*x+w*w*(1/(2-g)-1)/5


def log2_floor(q):
    n,d=q.numerator,q.denominator
    i=n.bit_length()-d.bit_length()
    if (n<d<<i if i>=0 else n<<(-i)<d):
        i-=1
    return i


def score(wz,wx,m):
    return log2_floor((wz*wz*wx)**(m*m))


def feature(block,m,mesh,idx):
    z,s,t=(F(i,mesh) for i in idx)
    chart=block.charts(z,s,t)
    if chart is None:
        return None
    x,Q=chart
    outer=2*block.k if z<F(1,2) else 4*block.k
    wz=cell_distance(z,outer)
    wx=cell_distance(x,block.n)
    # Isolate true bin boundaries and both physical doubling preimages. The
    # quarter power collar bounds logarithmic derivatives throughout survivors.
    if min(wz,wx)**4*mesh<=1 or min(wz,wx)*mesh<=8:
        return None
    if cell_distance(t,2*block.n)*mesh<=8:
        return None
    G=nested(x,wx,Q/3)
    E=nested(z,wz,G)
    return int(mesh*E),score(wz,wx,m),F(241,4)<2*block.k*z<F(243,4)


def solve(N,block):
    if N<1:
        raise ValueError('positive interval length required')
    answer=[1]
    for m in range(1,2*isqrt(N.bit_length())+3):
        mesh=1<<(10*m)
        if mesh<=(2*block.n)**4:
            continue
        table={idx:feature(block,m,mesh,idx) for idx in product(range(mesh),repeat=3)}
        candidate,_=extract(N,m,mesh,table,alphabet(mesh**2),3)
        if len(candidate)>len(answer):
            answer=candidate
    return answer

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('N',type=int);p.add_argument('table')
    args=p.parse_args();print(solve(args.N,Block(args.table)))
