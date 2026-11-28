"""Encode the lower 3D block from its defining inequalities, including every kink."""
import argparse
from fractions import Fraction as Q
from math import isqrt,lcm
from pathlib import Path
import sys

def raster(source,n,k,path):
    sys.path.insert(0,str(Path(source).resolve()))
    from verifica_parametro import F,G,J,V,R,Surd,q
    half=Q(1,2); zero=Surd(0)
    def floor(x):
        x=Surd.lift(x); d=lcm(x.a.denominator,x.b.denominator)
        a,b=int(d*x.a),int(d*x.b)
        r=isqrt(2*b*b)
        return (a+(r if b>=0 else -r-1))//d
    def edges(s,sheet):
        if sheet=='L':
            right=q*(1-R)*s
            return max(-half+q*R-q*R*s,right-half),right
        u=s-half
        right=q*(1-R)*u; left=half-q*R+q*R*u
        f=q*max(zero,F-u); g=q*max(zero,G-u)
        v=q*max(zero,V-u)/2
        if sheet=='+': return right,half-left-max(f,v)
        return -half+right+g,-left-v
    hinges=[R,half]+[half+x for x in (J,F,V,G,R)]
    layers=[min(Q(37,40),Q(9,20)+Q(11*t,20*(k-1))) for t in range(k)]
    out=bytearray([255])*(n*n)
    lower=0
    for i in range(n):
        s0,s1=Q(i,n),Q(i+1,n)
        if s1<=half:sheets=['L']
        elif s0>=half and s1<=half+R:sheets=['+','-']
        else:continue
        birth=next((h for h in range(k) if s1<=layers[h]),k)
        if birth==k:continue
        samples=[s0,s1]+[u for u in hinges if s0<u<s1]
        for sheet in sheets:
            cross=[edges(x,sheet) for x in samples]
            start=-floor(-n*max(a for a,b in cross))
            stop=floor(n*min(b for a,b in cross))
            for j in range(start,stop):
                idx=i*n+(j%n)
                assert out[idx]==255
                out[idx]=birth
                lower+=k-birth
    Path(path).write_bytes(out)
    print('lower cells',lower,'distinct inner squares',sum(b<k for b in out))

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('source');p.add_argument('n',type=int);p.add_argument('k',type=int);p.add_argument('output')
    a=p.parse_args();raster(a.source,a.n,a.k,a.output)
