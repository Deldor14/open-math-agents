"""Exact integer construction and volume of a torus block with growing clips."""
from bisect import bisect_left
from fractions import Fraction as Q
from pathlib import Path
import sys

def lower_rows(n,k,source):
    sys.path.insert(0,str(Path(source).resolve()))
    from verifica_parametro import Surd, Cell, half, R
    def ceil(v):
        # Smallest grid index at or above v, by exact comparison in Q(sqrt 2).
        a,b = -n,n
        while a<b:
            mid=(a+b)//2
            if Surd(Q(mid,n)) < v: a=mid+1
            else: b=mid
        return a
    cuts=[min(Q(37,40),Q(9,20)+Q(11*j,20*(k-1))) for j in range(k)]
    first=[];intervals=[]
    for i in range(n):
        l,r=Q(i,n),Q(i+1,n)
        bands=['L'] if r<=half else ['+','-'] if Surd(r)<=half+R else []
        pieces=[]
        for name in bands:
            cell=Cell(None,None,name)
            left=[cell.edges(Surd(u)) for u in (l,r)]
            a=ceil(max(v[0] for v in left))
            b=-ceil(-min(v[1] for v in left))
            if a<b: pieces.append((a,b))
        intervals.append(pieces)
        first.append(bisect_left(cuts,r))
    return first,intervals

def arc_mask(a,b,n):
    """Residues hit by the open angular interval (a,b) in integer bin units."""
    if b-a>=n: return (1<<n)-1
    a0=a%n; mask=((1<<(b-a))-1)<<a0
    return (mask | (mask>>n))&((1<<n)-1)

def best_window(vals):
    n=len(vals);d=n//2
    score=sum(vals[:d]);best=score;origin=0
    for j in range(1,n):
        score+=vals[(j+d-1)%n]-vals[j-1]
        if score>best: best,origin=score,j
    return best,origin

def widths_at_upper_row(n,k,p,first,parts):
    born=[0]*k
    for total in (p,(p-1)%n):
        for i in range(n):
            j=(total-i)%n
            if i>j:continue
            level=first[i]+first[j]
            if level>=k:continue
            for a,b in parts[i]:
                for c,d in parts[j]:
                    born[level] |= arc_mask(a+c,b+d,n)
    # A half-circle can be placed separately in each primary row.
    full=(1<<n)-1; forbidden=0;out=[]
    for new in born:
        forbidden |= new
        valid=full^forbidden
        # Reuse every repeated union along the outer coordinate.
        if out and valid==old:
            out.append(out[-1])
        else:
            # Shift a length-n/2 window by one, updating its integer population.
            bits=[(valid>>i)&1 for i in range(n)]
            out.append(best_window(bits))
        old=valid
    return out

def build(n,k,source,output=None):
    assert n%2==0 and k>=2
    first,parts=lower_rows(n,k,source)
    if output is not None:
        with Path(output).open('w') as f:
            print(n,k,file=f)
            for i,row in enumerate(parts):
                print(i,first[i],len(row),*(v for piece in row for v in piece),file=f)
    lower=sum((k-lev)*sum(b-a for a,b in row) for lev,row in zip(first,parts))
    columns=[widths_at_upper_row(n,k,p,first,parts) for p in range(n)]
    upper=sum(best_window([col[h][0] for col in columns])[0] for h in range(k))
    volume=Q(2*lower+upper,4*k*n*n)
    print('n, k, lower cells, upper cells:',n,k,lower,upper)
    print('limiting volume:',volume,float(volume))
    return volume
if __name__=='__main__':
    build(int(sys.argv[2]),int(sys.argv[3]),sys.argv[1],sys.argv[4] if len(sys.argv)>4 else None)
