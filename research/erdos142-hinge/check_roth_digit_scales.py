"""Integer checks for digit cuts, information and affine sampling."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import prod


def all_free(n):
    sets=[()]
    capacities=[0]
    for x in range(n):
        add=[]
        for a in sets:
            if all(2*y-x not in a for y in a):
                add.append(a+(x,))
        sets.extend(add)
        capacities.append(max(map(len,sets)))
    return sets,capacities


def least_columns(cols):
    full=0
    for bits in cols:
        full |= bits
    possible={0}
    for count in range(len(cols)+1):
        if full in possible:
            return count
        possible={p|c for p in possible for c in cols}
    raise AssertionError('uncovered row')


def rank_two(cols):
    pivot={}
    for bits in cols:
        while bits:
            i=bits.bit_length()-1
            if i not in pivot:
                pivot[i]=bits
                break
            bits ^= pivot[i]
    return len(pivot)


def cuts():
    d=4
    sets,r=all_free(2**d)
    partitions=0
    for a in sets[1:]:
        m=len(a)
        observed={}
        for j in range(1,d):
            w=2**j
            cols=[0]*(2**d//w)
            rows=Counter()
            sizes=Counter()
            for x in a:
                u,v=x%w,x//w
                cols[v] |= 1<<u
                rows[u]+=1
                sizes[v]+=1
            samples=least_columns(cols)
            rank=rank_two(cols)
            assert samples<=rank
            power_information=Fraction(m**m,prod(k**k for k in rows.values())*prod(k**k for k in sizes.values()))
            stable= sum((Fraction(1,rows[x%w]*sizes[x//w]) for x in a),Fraction())
            assert 1<=power_information<=stable**m
            observed[j]=(samples,power_information)
        for size in range(d):
            for js in combinations(range(1,d),size):
                endpoints=(0,)+js+(d,)
                capacity=prod(r[2**(v-u)] for u,v in zip(endpoints,endpoints[1:]))
                assert m<=capacity*prod(observed[j][0] for j in js)
                assert m**m<=capacity**m*prod(observed[j][1] for j in js)
                partitions+=1
    print('nonempty free sets at 16:',len(sets)-1,'cut selections:',partitions)


def affine():
    number=0
    maps=0
    for p in (17,19,31,37):
        n=(p-1)//2
        seeds=[a for a in [(0,), (0,1,3,4), (0,1,3,4,9,10,12,13)] if a[-1]<n]
        cells=[set(range(n)),set(range(0,n,2)),set(range(2,n,3)),set(),set(range(p))]
        for a in seeds:
            m=len(a)
            sums=[0]*len(cells)
            second=[0]*len(cells)
            for slope in range(1,p):
                for shift in range(p):
                    image={(slope*x+shift)%p for x in a}
                    crop=sorted(x for x in image if x<n)
                    assert all(2*y-x not in crop for x,y in combinations(crop,2))
                    for i,cell in enumerate(cells):
                        count=len(image&cell)
                        sums[i]+=count
                        second[i]+=(p*count-m*len(cell))**2
                    maps+=1
            for i,cell in enumerate(cells):
                c=len(cell)
                assert sums[i]==(p-1)*m*c
                assert second[i]==p*m*(p-m)*c*(p-c)
                number+=1
    print('affine maps:',maps,'exact variance identities:',number)


def information_power(a, j):
    m=len(a)
    w=2**j
    rows=Counter(x%w for x in a)
    cols=Counter(x//w for x in a)
    return Fraction(m**m,prod(r**r for r in rows.values())*prod(c**c for c in cols.values()))


def guarded_products():
    cases=0
    cuts_checked=0
    for t in (1,2,3):
        seeds,_=all_free(2**t)
        radix=2**(t+1)
        for u in seeds[1:]:
            for k in (1,2,3):
                a={sum(x*radix**i for i,x in enumerate(digits)) for digits in product(u,repeat=k)}
                assert len(a)==len(u)**k
                assert all(2*y-x not in a for x,y in combinations(sorted(a),2))
                for j in range(1,k*(t+1)):
                    expected=information_power(u,j%(t+1))**(len(a)//len(u))
                    assert information_power(a,j)==expected
                    cuts_checked+=1
                cases+=1
    print('guarded progression-free products:',cases,'exact cut informations:',cuts_checked)


if __name__=='__main__':
    cuts()
    affine()
    guarded_products()
