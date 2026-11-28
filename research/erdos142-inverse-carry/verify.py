"""Exact six-row duals and constants for the unrestricted carry bound."""
from fractions import Fraction as Q


def rows(n=6):
    return [(x,z,(x+z+n)//2) for x in range(n) for z in range(x,n-x)
            if (x+z+n)%2==0]


def coefficients(triples):
    return [[t.count(i) for i in range(6)] for t in triples]


def cost(matrix, multipliers, objective):
    weights = [Q(w) for w in multipliers]
    assert all(w>=0 for w in weights)
    loads = [sum(w*row[i] for w,row in zip(weights,matrix)) for i in range(6)]
    return sum(weights) + sum(max(0,tar-load) for tar,load in zip(objective,loads))/2


def main():
    tr=rows()
    assert tr==[(0,0,3),(0,2,4),(0,4,5),(1,1,4),(1,3,5),(2,2,5)]
    mat=coefficients(tr)
    lower_duals=[
        ('0 0 0 1/4 1/2 1/2','1/8'), ('0 1/3 2/3 0 0 1/3','1/6'),
        ('1/3 0 1/3 1/6 2/3 0','1/4'), ('0 0 1/2 1/2 0 1/2','1/4'),
        ('1/2 0 0 0 1/2 1/2','1/4'), ('1/4 1/2 0 1/2 0 0','1/8')]
    for i,(dual,expected) in enumerate(lower_duals):
        objective=[1]*6
        objective[i]=0
        assert 2-cost(mat,dual.split(),objective)==Q(expected)
    target=Q(1,80)
    assert Q(1,8)-target==9*target
    assert Q(527,10000)*(Q(1,2)-target)/2>target
    cases=[(0,3,1,'3/8 0 1/4 3/8 1/4 1/2',2,Q(1,28)),
           (5,2,2,'5/24 0 7/12 5/12 1/6 1/4',4,Q(1,32))]
    for row,i,extra,dual,error,expected in cases:
        modified=[r.copy() for r in mat]
        modified[row][i]+=extra
        weights=dual.split()
        total=cost(modified,weights,[1]*6)
        assert total==Q(31,16)
        assert (2-total)/(1+Q(weights[row])*error)==expected>target
    assert (2-target)/6==Q(53,160)
    print('Verified six row minima, both exact duals, inverse margins and cap 53/160.')


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled.')
    main()
