"""Enumerate small graph constraints independently of packed convolutions."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from graph import Graph, counts, extract_graph, pin_graph, weights
from extract import ZERO, clean, phase

def apfree(s):
    s=set(s)
    return all((a+b)%2 or (a+b)//2 not in s for a,b in combinations(s,2))

def graph_checks():
    n=5
    vertices=list(range(1,n+1))
    pairs=list(combinations(vertices,2))
    # {0,1,3} is independent for nonconstant modular 3-progressions mod 11.
    q,seed=11,{0,1,3}
    assert not any((2*y-x)%q in seed for y in seed for x in seed if x!=y)
    copies=Counter(tuple(v for v in vertices if (a*v+b)%q in seed)
                   for a in range(1,q) for b in range(q))
    for i,j in pairs:
        assert sum(k for s,k in copies.items() if i in s and j in s)==len(seed)*(len(seed)-1)
    graph_total=0
    for mask in range(1<<len(pairs)):
        g=Graph(n,vertices,[edge for j,edge in enumerate(pairs) if mask>>j&1])
        expected=Q(0)
        for s,k in copies.items():
            selected=g.select_independent(s)
            assert apfree(selected) and not any(a in selected and b in selected for a,b in g.edges)
            verify_potential=sum(Q(1,1+sum(y in s for y in g.neighbours[x])) for x in s)
            assert len(selected)>=verify_potential
            expected+=k*len(selected)
        lower=sum(Q(len(seed),q)/(1+Q(len(seed)-1,q-1)*len(g.neighbours[x])) for x in vertices)
        assert expected/(q*(q-1))>=lower
        colours={v:None if v==5 else (v%2,v%3,v==3) for v in vertices}
        _,plus,minus=weights(g,Q(5,17))
        totals=counts(g,colours,plus,minus)
        ts,te,tt=Counter(),Counter(),Counter()
        for v in vertices:
            if colours[v] is not None: ts[colours[v],]+=plus[v]
        for x,y in g.edges:
            if None not in (colours[x],colours[y]):te[colours[x],colours[y]]+=minus[x]+minus[y]
        for x,y in product(vertices,repeat=2):
            z=2*y-x
            if x!=z and z in vertices and None not in (colours[x],colours[y],colours[z]):
                tt[colours[x],colours[y],colours[z]]+=plus[y]
        assert totals==(ts,te,tt)
        graph_total+=1
    print(graph_total,'graphs over all 110 invertible affine maps; weighted colour counts checked')

def pin_checks():
    n=7; tested=0
    for mask in range(1<<n):
        pos={v for v in range(1,n+1) if mask>>(v-1)&1}
        if not apfree(pos):continue
        for ban in (set(),{n}-pos):
            g=pin_graph(n,pos,ban)
            for k in range(1<<len(g.vertices)):
                s={v for j,v in enumerate(g.vertices) if k>>j&1}
                full=pos|s
                predicted=apfree(s) and not any(x in s and y in s for x,y in g.edges)
                assert predicted==apfree(full) and ban.isdisjoint(full)
                tested+=1
            for v in set(range(1,n+1))-set(g.vertices)-ban-pos:
                assert not apfree(pos|{v})
    print(tested,'prescription and extension comparisons')

def extraction():
    n,p,mesh=5,127,2
    options={(tuple(phase((p,a,b),i,mesh) for i in range(1,n+1))):(p,a,b)
             for a in range(p) for b in range(p)}
    labels={(x,y):(x-y,2*x+y,x==y==0) if (x,y)!=(1,1) else None
            for x,y in product(range(mesh),repeat=2)}
    tests=[Graph(n,range(1,n+1),[(1,2),(1,3),(2,5)]),
           Graph(n,[1,2,4,5],[(1,5)]),pin_graph(n,{1})]
    for g in tests:
        got,tr=extract_graph(g,2,mesh,labels,options.values())
        assert apfree(got) and all(not(x in got and y in got) for x,y in g.edges)
        assert len(got)>=tr[-1] and all(x<=y for x,y in zip(tr,tr[1:]))
        if g is tests[-1]:assert apfree(set(got)|{1})
    print('Three finite weighted optimizations, including pins; all estimator steps monotone.')

if __name__=='__main__':
    graph_checks();pin_checks();extraction()
