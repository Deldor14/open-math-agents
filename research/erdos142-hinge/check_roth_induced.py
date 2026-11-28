"""Independent finite checks for isolated triples, counts and changes of scale."""
from itertools import combinations, product
from math import comb, lcm
from collections import Counter


def aps(points):
    points = set(points)
    return {(x,y,2*y-x) for x in points for y in points if x<y and 2*y-x in points}


def defect_free(points,t):
    for x,y,z in combinations(points,3):
        total=x+y+z
        if any(abs(total-3*v) in (0,t,2*t) for v in (x,y,z)):
            return False
    return True


def free_sets(n):
    family = [()]
    for v in range(n):
        family += [s+(v,) for s in family if all(2*y-v not in s for y in s)]
    return family


def maximal_sets(n,family):
    all_sets = {frozenset(s) for s in family}
    universe = set(range(n))
    return {s for s in all_sets if all(s|{x} not in all_sets for x in universe-s)}


def check():
    small = {n:free_sets(n) for n in range(20)}
    numbers = [max(map(len,small[n])) for n in small]
    maximal = [maximal_sets(n,small[n]) for n in small]
    for n in range(20):
        assert len(maximal[n]) >= 3**numbers[n//5]
    examples = spectra = residues = fourfold = maximal_tests = 0
    for s in small[14]:
        n=max(s,default=-1)+1
        for t in range(1,6):
            if not defect_free(s,t):
                continue
            anchors=[x for x in s if x+t in s]
            if not anchors:
                continue
            fibers=[frozenset((x,x+t,x+2*t)) for x in anchors]
            U=set.union(set(),*fibers)
            assert len(U)==3*len(anchors)
            assert aps(U)=={tuple(sorted(f)) for f in fibers}
            for x,y,z in product(anchors,repeat=3):
                d=x+z-2*y
                assert d%t or abs(d)>4*t or x==y==z
            examples+=1
            counts=Counter()
            for k in range(len(U)+1):
                counts[k]=sum(not aps(c) for c in combinations(U,k))
            exact=[1]
            for _ in anchors:
                new=[0]*(len(exact)+2)
                for i,count in enumerate(exact):
                    for j in range(3):
                        new[i+j]+=comb(3,j)*count
                exact=new
            assert all(counts[k]==(exact[k] if k<len(exact) else 0) for k in range(len(U)+1))
            assert sum(exact)==7**len(anchors)
            spectra+=1
            for b in range(2,13):
                if t%b==0:
                    continue
                for r in range(b):
                    quotient={x//b for x in U if x%b==r}
                    assert not aps(quotient)
                    assert all(x < (n+t+b-1)//b for x in quotient)
                assert len(U)<=b*numbers[(n+t+b-1)//b]
                residues+=1
            expanded={x+t*(x//t+d) for x in anchors for d in (0,1,3,4)}
            assert len(expanded)==4*len(anchors) and not aps(expanded)
            assert max(expanded)<2*n+2*t
            fourfold+=1
            if n+t<=11:
                witnessed=set()
                for omit in product(range(3),repeat=len(anchors)):
                    choice=frozenset().union(*(f-{sorted(f)[i]} for f,i in zip(fibers,omit)))
                    extension=next(S for S in maximal[n+t] if choice<=S)
                    assert extension not in witnessed
                    witnessed.add(extension)
                assert len(witnessed)==3**len(anchors)
                maximal_tests+=1
    print('Admissible nonempty collections of isolated triples:',examples)
    print('Independence polynomials checked by subset enumeration:',spectra)
    print('Residue inequalities and four-point lifts:',residues,fourfold)
    print('Distinct maximal extensions, checked families:',maximal_tests)
    print('Maximal interval counts at lengths 0 through 19:', [len(s) for s in maximal])

    multiple = 1
    for s in range(1,257):
        multiple = lcm(multiple,s)
        assert 2**s <= (s+1)*multiple
    for L in range(3,33):
        # Exact integer Bernoulli comparison used after L dyadic transitions.
        assert 20*(20*L-1)**L >= 19*(20*L)**L
    # N=2^j. Choose the least Q=2^L >=32 log_2(2N), with exact arithmetic.
    for j in range(2,1026):
        Q = 1 << (32*(j+1)-1).bit_length()
        s = Q//8
        assert (s+1)*Q*2**j < 2**s
    print('LCM, Bernoulli and terminal-gap checks:',256,30,1024)


if __name__=='__main__':
    check()
