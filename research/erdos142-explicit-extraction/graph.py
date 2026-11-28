"""Joint deterministic avoidance of 3-APs and an arbitrary simple conflict graph."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from heapq import heapify, heappop, heappush
from itertools import product
from math import isqrt
from pathlib import Path
import sys
from extract import (ZERO, add, alphabet, clean, fast_product, haar, passes, phase,
                     residual_laws, accepted_count)

class Graph:
    def __init__(self,n,vertices,edges):
        self.n=n
        self.vertices=sorted(set(vertices))
        if n<1 or any(i<1 or i>n for i in self.vertices):
            raise ValueError('vertices must be in [1,N]')
        self.neighbours={v:set() for v in self.vertices}
        for x,y in edges:
            if x==y or x not in self.neighbours or y not in self.neighbours:
                raise ValueError('each edge must join two distinct supplied vertices')
            self.neighbours[x].add(y)
            self.neighbours[y].add(x)
        self.edges=[(x,y) for x in self.vertices for y in self.neighbours[x] if x<y]

    def select_independent(self,sites):
        live=set(sites)
        deg={x:sum(v in live for v in self.neighbours[x]) for x in live}
        heap=[(k,x) for x,k in deg.items()]
        heapify(heap)
        chosen=[]
        while heap:
            d,x=heappop(heap)
            if x not in live or d!=deg[x]: continue
            chosen.append(x)
            gone={x}|(self.neighbours[x]&live)
            live-=gone
            for y in gone:
                for z in self.neighbours[y]:
                    if z in live:
                        deg[z]-=1
                        heappush(heap,(deg[z],z))
        return sorted(chosen)

def weights(graph,p):
    scale=1 << (10*(graph.n+1).bit_length())
    plus,minus={},{}
    for x in graph.vertices:
        t=p*len(graph.neighbours[x])
        a=scale*(1+2*t)/(1+t)**2
        b=scale/(1+t)**2
        plus[x]=a.numerator//a.denominator
        minus[x]=-(-b.numerator//b.denominator)
    return scale,plus,minus

def counts(graph,colours,plus,minus):
    """Sum integer weights over occupied prefixes. Sites are 1-based."""
    n=graph.n
    groups={}
    single,edges,triples=Counter(),Counter(),Counter()
    for v in graph.vertices:
        c=colours[v]
        if c is not None:
            groups.setdefault(c,[]).append(v)
            single[c,]+=plus[v]
    for v,w in graph.edges:
        a,c=colours[v],colours[w]
        if a is not None and c is not None:
            edges[a,c]+=minus[v]+minus[w]
    width=max(1,(n.bit_length()+7)//8)
    packed={}
    for c,indices in groups.items():
        buff=bytearray((n+1)*width)
        for v in indices: buff[v*width]=1
        packed[c]=int.from_bytes(buff,'little')
    for a,va in packed.items():
        for c,vc in packed.items():
            coeffs=fast_product(va,vc).to_bytes((2*n+1)*width,'little')
            for b,sites in groups.items():
                score=sum(plus[v]*int.from_bytes(coeffs[2*v*width:(2*v+1)*width],'little') for v in sites)
                if a==b==c: score-=single[b,]
                if score: triples[a,b,c]=score
    return single,edges,triples

def continuation(prefix,laws,r,eta,param,scale):
    one,two,three=prefix
    slaw,tlaw=laws[0][r],laws[1][r]
    def single_prob(colour):
        return accepted_count({(colour,):1},slaw,param)
    cache={x:single_prob(x) for x, in one}
    pairs=sum(w*cache[a]*cache[b] for (a,b),w in two.items())
    return ((1-eta)**r*accepted_count(one,slaw,param)
            -(1+eta)**r*(pairs+accepted_count(three,tlaw,param)))/scale

def extract_graph(graph,m,mesh,table,choices):
    """Choose common score and window, then fix each physical block by averaging."""
    n=graph.n
    if not graph.vertices: return [],[]
    single,triple=haar(table,mesh)
    if not any(k[0][2] for k in single[0]):return [],[]
    laws=residual_laws(single,m,1),residual_laws(triple,m,3)
    full,den=laws[0][m]
    eligible=[k[0] for k in full if k[0][2]]
    energies=sorted({c[0] for c in eligible})
    thresholds=sorted({c[1] for c in eligible})
    eta=Q(1,(m+1)**2)
    prefix={v:ZERO for v in graph.vertices}
    best,param_weights=None,None
    for k,lo in enumerate(energies):
        for hi in energies[k:]:
            for cut in thresholds:
                param=(lo,hi,cut)
                p=Q(sum(w for (a,),w in full.items() if passes(a,param)),den)
                if not p:continue
                scale,plus,minus=weights(graph,p)
                v=continuation(counts(graph,prefix,plus,minus),laws,m,eta,param,scale)
                if best is None or v>best:
                    best,param_weights=v,(param,scale,plus,minus)
    if param_weights is None:return [],[]
    param,scale,plus,minus=param_weights
    history=[best];scalar=list(choices)
    for k in range(1,m+1):
        maximum=None
        for a,b in product(scalar,repeat=2):
            curr={v:add(c,table[phase(a,v,mesh),phase(b,v,mesh)]) for v,c in prefix.items()}
            val=continuation(counts(graph,curr,plus,minus),laws,m-k,eta,param,scale)
            if maximum is None or val>maximum:
                maximum,keep=val,curr
        prefix=keep
        history.append(maximum)
    cleaned=clean([v for v,c in prefix.items() if passes(c,param)])
    return graph.select_independent(cleaned),history

def pin_graph(n,required,excluded=()):
    positive,negative=set(required),set(excluded)
    if any(x<1 or x>n for x in positive|negative) or positive&negative:
        raise ValueError('incompatible site prescriptions')
    if set(clean(positive))!=positive:
        raise ValueError('required sites contain a progression')
    blocked=positive|negative
    for a in positive:
        for b in positive:
            if a>=b:continue
            blocked.update((2*a-b,2*b-a))
            if (a+b)%2==0:blocked.add((a+b)//2)
    allowed=set(range(1,n+1))-blocked
    def conflicts():
        for p in positive:
            for x in allowed:
                options=[2*p-x,2*x-p]
                if (x+p)%2==0:options.append((x+p)//2)
                for y in options:
                    if y in allowed and x<y:yield x,y
    return Graph(n,allowed,conflicts())

def solve_graph(graph,geometry):
    sys.path.insert(0,str(Path(geometry).resolve()))
    from curved import CurvedTable
    best=graph.vertices[:1]
    for m in range(1,2*isqrt(graph.n.bit_length())+3):
        mesh=1<<(10*m)
        profile=CurvedTable(m,mesh)
        if profile.tau+Q(8,mesh)>=Q(1,20):continue
        table={(i,j):profile.at(i,j) for i,j in product(range(mesh),repeat=2)}
        got,_=extract_graph(graph,m,mesh,table,alphabet(mesh**2))
        if len(got)>len(best):best=got
    return best

if __name__=='__main__':
    import json
    p=argparse.ArgumentParser()
    p.add_argument('input',help='JSON with N, vertices, edges or N, required, excluded')
    p.add_argument('geometry')
    args=p.parse_args()
    data=json.loads(Path(args.input).read_text())
    if 'required' in data:
        g=pin_graph(data['N'],data['required'],data.get('excluded',[]))
        print(sorted(set(data['required'])|set(solve_graph(g,args.geometry))))
    else:
        print(solve_graph(Graph(data['N'],data['vertices'],data['edges']),args.geometry))
