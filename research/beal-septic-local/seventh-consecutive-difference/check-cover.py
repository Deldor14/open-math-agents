"""Replay the published witnesses directly on residues of each successive exponent."""
from math import isqrt
from pathlib import Path

here = Path(__file__).resolve().parent
rows = [list(map(int,row.split())) for row in (here/"cover.txt").read_text().splitlines()]
assert [r[:3] for r in rows] == [list(map(int,s.split()))
                                  for s in (here/"classes.txt").read_text().splitlines()]
tested = 0
for d,v,r,*qs in rows:
    exps = range(r if r!=1 else r+5040, 300000000, 5040)
    tested += len(exps)
    for q in qs:
        assert all(q%i for i in range(2,isqrt(q)+1)) and d%q
        allowed = set()
        for a in range(q):
            u=a*(a+1)
            allowed.add((1+7*u*(u+1)**2)%q)
        base = v*pow(pow(d,6,q),-1,q)%q
        allowed_powers = [pow(base,k if k else q-1,q) in allowed for k in range(q-1)]
        exps = [n for n in exps if allowed_powers[n%(q-1)]]
    assert not exps, (d,v,r)
print(len(rows), "rows;", tested, "exponent candidates excluded")
