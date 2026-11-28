"""Independently generate endpoint clauses and verify both sides with CaDiCaL."""
import shutil
import subprocess
import sys
from math import gcd


def status(n,p,solver):
    clauses=[]
    for first in range(n):
        for last in range(first+1,n):
            span=last-first
            if span%2==0:
                clauses.append((-(first+1),-((first+last)//2+1),-(last+1)))
            if span%(p-1)==0:
                q=span//(p-1)
                if gcd(q,p)==1:
                    clauses.append(tuple(x+1 for x in range(first,last+1,q)))
    data='p cnf {} {}\n'.format(n,len(clauses))+''.join(' '.join(map(str,row))+' 0\n' for row in clauses)
    run=subprocess.run([solver,'-q'],input=data,text=True,capture_output=True,check=False)
    assert run.returncode in (10,20),run.stderr
    return run.returncode==10


if __name__=='__main__':
    solver=sys.argv[1] if len(sys.argv)>1 else shutil.which('cadical')
    if not solver:
        raise SystemExit('Pass a path to the CaDiCaL executable.')
    for p,n in ((2,6),(3,13),(5,23),(7,51)):
        assert status(n-1,p,solver) and not status(n,p,solver)
        print('p={}, satisfiable through {}, unsatisfiable at {}'.format(p,n-1,n))
