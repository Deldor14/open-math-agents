"""Generate the final paired-grid duals after running build_duals.py twice."""
from fractions import Fraction
from pathlib import Path
import gzip
import json
import numpy as np
from scipy.optimize import linprog
from bohr_check import check, merges, triples, known_row
from build_duals import dual_key


def generate(root):
    survivors=check(root/'near_certificate.json.gz',Fraction(143,480),True)
    nodes=[];duals=[];index={}
    for aa in survivors:
        for bb in survivors:
            a=[[2*x for x in g] for g in aa]
            b=[[2*x+1 for x in g] for g in bb]
            active=[x for g in a+b for x in g]
            rows=triples(24,sum(1<<x for x in active))
            def certify(rankings):
                mat=np.zeros((len(rows),24),dtype=int)
                for j,row in enumerate(rows):
                    for k,v in zip(row,map(max,zip(*(known_row(row,g) for g in rankings)))):
                        mat[j,k]+=v
                result=linprog(-np.ones(24),A_ub=mat,b_ub=np.ones(len(rows)),
                               bounds=[(0,.5 if x in active else 0) for x in range(24)],
                               method='highs')
                assert result.success
                if -result.fun > 7.2+1e-8:return False
                key=dual_key(result)
                if key not in index:index[key]=len(duals);duals.append(key)
                nodes.append(index[key])
                return True
            if not certify([a,b]):
                nodes.append(-1)
                for g in merges(a,b):assert certify([g])
    data=json.dumps(dict(nodes=nodes,duals=duals),separators=(',',':')).encode()
    (root/'paired_certificate.json.gz').write_bytes(gzip.compress(data,mtime=0))

if __name__=='__main__':generate(Path(__file__).resolve().parent)
