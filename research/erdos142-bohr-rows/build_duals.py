"""Generate a tree of rational LP duals; bohr_check.py verifies them separately."""
import gzip
import json
import sys
from fractions import Fraction
from functools import reduce
from math import gcd
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from bohr_check import triples, known_row, children, active_indices, rank_order


def lcm(a,b):
    return a//gcd(a,b)*b


def dual_key(rs):
    weights=[Fraction(float(max(0,-v))).limit_denominator(1000000)
             for v in rs.ineqlin.marginals]
    d=reduce(lcm,(w.denominator for w in weights),1)
    return d,tuple((j,int(w*d)) for j,w in enumerate(weights) if w)


def generate(n, target, path):
    nodes = []; duals = []; index = {}
    for mask in range(1<<n):
        active = active_indices(n,mask)
        if Fraction(len(active),2)<=n*target: continue
        rows = triples(n,mask)
        order = rank_order(active,rows)
        bounds = [(0,.5 if i in active else 0) for i in range(n)]

        def visit(groups,depth):
            mat = np.zeros((len(rows),n),dtype=int)
            for j,t in enumerate(rows):
                for k,v in zip(t,known_row(t,groups)):
                    mat[j,k]+=v
            rs=linprog(-np.ones(n),A_ub=mat,b_ub=np.ones(len(rows)),
                       bounds=bounds,method='highs')
            assert rs.success
            if -rs.fun<=float(n*target)+1e-8:
                key=dual_key(rs)
                if key not in index:
                    index[key]=len(duals);duals.append(key)
                nodes.append(index[key])
            else:
                if depth==len(order):
                    assert n==12 and target==Fraction(143,480)
                    nodes.append(-2)
                    return
                nodes.append(-1)
                for g in children(groups,order[depth]):visit(g,depth+1)
        visit([],0)
    obj=dict(grid=n,cap=str(target),nodes=nodes,duals=duals)
    if n==12 and target==Fraction(29,96):
        obj['witness']={'levels':[0,1,1,1,1,1,1,2,2,2,2,0],
                        'widths':['1/24','1/12','1/4','1/3','5/12','1/2','1/2','1/2','1/2','1/3','1/6','0']}
    path.write_bytes(gzip.compress(json.dumps(obj,separators=(',',':')).encode(),mtime=0))
    print(path, len(nodes), len(duals), path.stat().st_size,flush=True)


if __name__=='__main__':
    generate(int(sys.argv[1]), Fraction(sys.argv[2]), Path(sys.argv[3]))
