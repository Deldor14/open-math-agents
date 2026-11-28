"""Recompute layer marginals and a directed lower comparison on the cubical shell scale."""
import hashlib
import sys
from pathlib import Path
from fractions import Fraction as Q
from mpmath import iv

def main(source):
    sys.path.insert(0,str(source.resolve()))
    from build import widths_at_upper_row, best_window
    data = (source/'lower.tsv').read_bytes()
    assert hashlib.sha256(data).hexdigest()=="0f7e9544ddb1016ab417922240d1fd72072416005c8ce1a193862d3a90068536"
    rows = [list(map(int,line.split())) for line in data.splitlines()]
    n,k = rows[0]
    assert (n,k)==(2048,96)
    first=[]; parts=[]
    for i,row in enumerate(rows[1:]):
        j,lev,count,*ends=row
        assert j==i and len(ends)==2*count
        first.append(lev)
        parts.append(list(zip(ends[::2],ends[1::2])))
    assert len(first)==n
    born=[0]*(k+1)
    for lev,arcs in zip(first,parts):
        born[lev]+=sum(r-l for l,r in arcs)
    below=[sum(born[:i+1]) for i in range(k)]
    cols=[widths_at_upper_row(n,k,p,first,parts) for p in range(n)]
    above=[best_window([c[h][0] for c in cols])[0] for h in range(k)]
    assert (sum(below),sum(above))==(98713058,75594412)
    bands=[(Q(i,2*k),Q(i+1,2*k),w) for i,w in enumerate(below)]
    bands.extend((Q(1,2)+Q(i,4*k),Q(1,2)+Q(i+1,4*k),w) for i,w in enumerate(above))
    rho=Q(17063783,100663296)
    def moment(power):
        return sum(w*(r**(power+1)-l**(power+1)) for l,r,w in bands)/((power+1)*n*n*rho)
    assert moment(0)==1
    var=moment(4)-moment(2)**2
    assert var==Q(11870020553967429116996507,569794228641089071727247360)
    p=Q(sum(above),2*sum(below)+sum(above))
    iv.dps=40
    def real(q):return iv.mpf(q.numerator)/q.denominator
    log=iv.log
    score=3+2*log(4*k)+2*real(p)*log(2)+log(2*n)
    det=iv.sqrt(4*320*9600)
    width=real(rho)**(-real(Q(1,3)))*3/(4*iv.pi*iv.exp(1))*iv.exp(-real(Q(2,3))*(score+log(det)))
    sigma=iv.sqrt(real(var))+real(Q(1,160*k*k))
    dim=(2/(3*log(1/real(rho))))**real(Q(1,4))
    coefficient=width*dim/(sigma*iv.sqrt(2*iv.pi))
    print('sha256:',hashlib.sha256(data).hexdigest())
    print('upper mass fraction:',p,'variance z²:',var)
    print('mean log loss:',score,'window factor:',width,'sigma upper comparison:',sigma,
          'liminf lower comparison:',coefficient,sep='\n')
    assert coefficient.a>real(Q(218,10**12)).b

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled.')
    main(Path(sys.argv[1]))
