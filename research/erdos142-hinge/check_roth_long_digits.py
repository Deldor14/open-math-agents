"""Exact digit inequalities for k-AP-free sets and heterogeneous products."""
from itertools import combinations
from math import prod
from check_roth_digit_scales import information_power


def free_sets(n,k):
    family=[()]
    capacities=[0]
    for z in range(n):
        new=[]
        for a in family:
            if all(any(z-i*step not in a for i in range(1,k)) for step in range(1,z//(k-1)+1)):
                new.append((*a,z))
        family.extend(new)
        capacities.append(max(map(len,family)))
    return family,capacities


def free(points,k):
    a=set(points)
    n=max(a,default=0)
    return not any(all(x+i*step in a for i in range(1,k)) for x in a for step in range(1,(n-x)//(k-1)+1))


def cutoff_bound():
    choices=[c for length in range(4) for c in combinations((1,2,3),length)]
    for k in (4,5,6):
        family,r=free_sets(16,k)
        for a in family[1:]:
            m=len(a)
            powers={j:information_power(a,j) for j in (1,2,3)}
            for cuts in choices:
                ends=(0,*cuts,4)
                cap=prod(r[2**(v-u)] for u,v in zip(ends,ends[1:]))
                assert m**m <= cap**m*prod(powers[j] for j in cuts)
        print(f'k={k}: {len(family)-1} free subsets, {(len(family)-1)*len(choices)} information inequalities')


def heterogeneous():
    count=tests=0
    for k in (3,4,5,6):
        left,_=free_sets(4,k)
        right,_=free_sets(8,k)
        for u in left[1:]:
            for v in right[1:]:
                a={x+8*y for x in u for y in v}
                assert len(a)==len(u)*len(v) and free(a,k)
                for j in range(1,6):
                    expected=(information_power(u,j)**len(v) if j<=3
                              else information_power(v,j-3)**len(u))
                    assert information_power(a,j)==expected
                    tests+=1
                count+=1
    print(f'{count} mixed products, {tests} exact split information identities')


if __name__=='__main__':
    cutoff_bound()
    heterogeneous()
