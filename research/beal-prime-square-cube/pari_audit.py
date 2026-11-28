"""Stream source rows to PARI, which computes j in its elliptic curve library."""
from pathlib import Path
import subprocess
import sys

directory=Path(sys.argv[1])
gp=sys.argv[2]
script=Path(__file__).with_name('check_cremona.gp')
with subprocess.Popen([gp,'-fq',str(script)],stdin=subprocess.PIPE,text=True) as proc:
    proc.stdin.write('audit()\n')
    total=0
    for path in sorted(directory.glob('allcurves.*')):
        for row in path.open():
            level,_,_,model,*_ = row.split()
            N=int(level)
            while N%2==0:
                N//=2
            while N%3==0:
                N//=3
            if N>1:
                proc.stdin.write('['+level+','+model[1:]+'\n')
            total+=1
    proc.stdin.write('0\nquit\n')
    proc.stdin.close()
    rc=proc.wait()
assert total == 3064705 and rc==0
