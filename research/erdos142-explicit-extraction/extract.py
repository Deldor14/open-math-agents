"""Finite conditional expectations with exact Haar histograms and coloured AP counts.

The theoretical mesh is intentionally very large. Use verify.py for runnable
small instances of the same estimator. No numerical FFT or real logarithms.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import factorial, isqrt
from pathlib import Path
import sys

ZERO = (0,0,False)

def add(x,y):
    if x is None or y is None:
        return None
    return x[0]+y[0], x[1]+y[1], x[2] or y[2]

def passes(x, param):
    lo,hi,threshold = param
    return x is not None and lo <= x[0] <= hi and x[1] >= threshold and x[2]

def phase_cells(mesh):
    for i in range(mesh):
        for j in range(mesh):
            for offset,weight in ((-1,1),(0,2),(1,1)):
                yield (i,j,(2*j-i+offset)%mesh),weight

def haar(table,mesh):
    sites = Counter((v,) for v in table.values() if v is not None)
    triples = Counter()
    for (a,wa),(b,wb) in product(phase_cells(mesh),repeat=2):
        t = tuple(table[i,j] for i,j in zip(a,b))
        if None not in t:
            triples[t] += wa*wb
    return (sites,mesh**2),(triples,(4*mesh**2)**2)

def residual_laws(one,m,arity):
    counts,den = one
    levels = [(Counter({(ZERO,)*arity:1}),1)]
    for _ in range(m):
        prev,d = levels[-1]
        nxt = Counter()
        for a,wa in prev.items():
            for b,wb in counts.items():
                nxt[tuple(add(x,y) for x,y in zip(a,b))] += wa*wb
        levels.append((nxt,d*den))
    return levels

def fast_product(x,y):
    """Integer Toom multiplication with a growing number of evaluation points."""
    length = max(x.bit_length(),y.bit_length())
    if length <= 8192 or not x or not y:
        return x*y
    radix = max(2,isqrt(length.bit_length()))
    width = (length+radix-1)//radix
    mask = (1 << width)-1
    def chunks(v):
        return [(v >> (i*width)) & mask for i in reversed(range(radix))]
    def evaluate(parts,t):
        result = 0
        for part in parts:
            result = result*t+part
        return result
    a,b = chunks(x),chunks(y)
    row = [fast_product(evaluate(a,t),evaluate(b,t)) for t in range(2*radix-1)]
    coeffs = []
    while row:
        coeffs.append(row[0]//factorial(len(coeffs)))
        row = [right-left for left,right in zip(row,row[1:])]
    result = 0
    for i in reversed(range(len(coeffs))):
        result = (result << width)-i*result+coeffs[i]
    return result


def colour_counts(colours):
    """Single-site and ordered, distinct-endpoint AP histograms in the input interval."""
    n = len(colours)
    locations = defaultdict(list)
    for i,v in enumerate(colours):
        if v is not None:
            locations[v].append(i)
    singles = Counter({(v,):len(indices) for v,indices in locations.items()})
    triples = Counter()
    word = max(1,(n.bit_length()+7)//8)
    packed = {}
    for v,indices in locations.items():
        block = bytearray(n*word)
        for i in indices:
            block[i*word] = 1
        packed[v] = int.from_bytes(block,'little')
    for a,va in packed.items():
        for c,vc in packed.items():
            coeffs = fast_product(va,vc).to_bytes((2*n-1)*word,'little')
            for b,indices in locations.items():
                count = sum(int.from_bytes(coeffs[2*i*word:(2*i+1)*word],'little') for i in indices)
                if a == b == c:
                    count -= len(indices)
                if count:
                    triples[a,b,c] = count
    return singles,triples

def accepted_count(prefix, law, param):
    residual,den = law
    numerator = sum(np*nr for p,np in prefix.items() for r,nr in residual.items()
                    if all(passes(add(a,b),param) for a,b in zip(p,r)))
    return Fraction(numerator,den)

def value(counts, laws, remaining, epsilon, param):
    return ((1-epsilon)**remaining*accepted_count(counts[0],laws[0][remaining],param)
            -(1+epsilon)**remaining*accepted_count(counts[1],laws[1][remaining],param))

def alphabet(bound):
    """Each (prime, slope, shift) is an equally weighted scalar choice."""
    prime = bytearray([1])*(2*bound+1)
    prime[:2] = bytes(2)
    for p in range(2,isqrt(2*bound)+1):
        if prime[p]:
            prime[p*p::p] = bytes((2*bound-p*p)//p+1)
    for p in range(bound,2*bound+1):
        if prime[p]:
            yield from ((p,a,b) for a in range(p) for b in range(p))

def phase(choice,i,mesh):
    p,a,b = choice
    return ((a*i+b)%p)*mesh//p

def clean(sites):
    if not sites:
        return []
    n = max(sites)
    word = max(1,(n.bit_length()+7)//8)
    bits = bytearray((n+1)*word)
    for i in sites:
        bits[i*word] = 1
    v = int.from_bytes(bits,'little')
    square = fast_product(v,v).to_bytes((2*n+1)*word,'little')
    return [i for i in sites if int.from_bytes(square[2*i*word:(2*i+1)*word],'little') == 1]

def extract(n,m,mesh,table,choices):
    one,three = haar(table,mesh)
    if not any(k[0][2] for k in one[0]):
        return [], []
    laws = residual_laws(one,m,1),residual_laws(three,m,3)
    initial = [ZERO]*n
    counts = colour_counts(initial)
    totals = [k[0] for k in laws[0][m][0] if k[0][2]]
    energies = sorted({x[0] for x in totals})
    scores = sorted({x[1] for x in totals})
    epsilon = Fraction(1,(m+1)**2)
    start, selected = None, None
    for i,lo in enumerate(energies):
        for hi in energies[i:]:
            for q in scores:
                param = lo,hi,q
                v = value(counts,laws,m,epsilon,param)
                if start is None or v > start:
                    start,selected = v,param
    if selected is None:
        return [], []
    prefix, trace = initial,[start]
    scalar = list(choices)
    for k in range(1,m+1):
        best, chosen = None, None
        for a,b in product(scalar,repeat=2):
            candidate = [add(x,table[phase(a,i,mesh),phase(b,i,mesh)])
                         for i,x in enumerate(prefix,1)]
            v = value(colour_counts(candidate),laws,m-k,epsilon,selected)
            if best is None or v > best:
                best,chosen = v,candidate
        trace.append(best)
        prefix = chosen
    return clean([i for i,x in enumerate(prefix,1) if passes(x,selected)]), trace

def solve(n,geometry,profile="curved"):
    if n < 1:
        raise ValueError('N must be positive')
    sys.path.insert(0,str(Path(geometry).resolve()))
    from tents import TentTable
    from curved import CurvedTable
    table_type = {"tents":TentTable,"curved":CurvedTable}[profile]
    best = [1]
    for m in range(1,2*isqrt(n.bit_length())+3):
        mesh = 1 << (10*m)
        geom = table_type(m,mesh)
        # For small H the removed primary collar covers the marked rectangle.
        if geom.tau + Fraction(8,mesh) >= Fraction(1,20):
            continue
        table = {(i,j):geom.at(i,j) for i,j in product(range(mesh),repeat=2)}
        result,_ = extract(n,m,mesh,table,alphabet(mesh**2))
        if len(result)>len(best):
            best = result
    return best

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('N',type=int)
    p.add_argument('geometry',help='directory with verifica_parametro.py and verifica_poligono.py')
    p.add_argument("--profile",choices=("curved","tents"),default="curved")
    args = p.parse_args()
    print(solve(args.N,args.geometry,args.profile))
