import pathlib,sys,json,time
from pysat.solvers import Cadical195
root=pathlib.Path(__file__).resolve().parent
m,goal,budget,sec=map(int,sys.argv[1:5]);data=pathlib.Path(sys.argv[5]);tag=sys.argv[6]
need=goal-m;n=74
cap={0:0,**dict(tuple(map(int,l.split())) for l in (root/'r6-through-147.txt').read_text().splitlines() if l)}
clauses=[];V=n
def var():
 global V
 V+=1;return V
def neg(x):return not x if type(x)==bool else -x
def cl(*v):
 if not any(x is True for x in v):clauses.append([x for x in v if x is not False])
for d in range(1,15):
 for a in range(1,75-5*d):clauses.append([-(a+j*d) for j in range(6)])
activate={}
for d in range(1,30,2):
 for a in range(74-2*d):
  z=var();activate[a,d]=z;clauses.append([-z,-(a+1),-(a+d+1),-(a+2*d+1)])
prefix={}
for step in range(1,9):
 groups=[list(range(a,75,step)) for a in range(1,step+1)];s=sum(cap[len(g)] for g in groups)
 for xs in groups:
  L=len(xs);required=need-s+cap[L]
  if required<=0:continue
  hi=[min(need,cap[i]) for i in range(L+1)]
  lo=[max(0,required-cap[L-i]) for i in range(L+1)]
  rows=[{h:var() for h in range(lo[i]+1,hi[i]+1)} for i in range(L+1)]
  def ge(i,h):return True if h<=lo[i] else False if h>hi[i] else rows[i][h]
  if step==1:prefix={(i,h):ge(i,h) for i in range(L+1) for h in range(need+2)}
  for i,x in enumerate(xs,1):
   for h in range(max(1,lo[i-1]),hi[i-1]+3):
    p,q,t=ge(i-1,h),ge(i-1,h-1),ge(i,h)
    cl(neg(p),t);cl(neg(q),-x,t);cl(neg(t),x,p);cl(neg(t),q)
  for j in range(2,L+1):
   for i in range(j-1):
    c=cap[j-i]
    for h in range(max(lo[i]+1,lo[j]-c),hi[j]-c+1):cl(neg(ge(j,h+c)),ge(i,h))
start=time.monotonic();out=root/f'parity_{tag}.jsonl'
with Cadical195(bootstrap_with=clauses) as solver,out.open('w',buffering=1) as dest,data.open() as inp:
 for idx,line in enumerate(inp):
  if time.monotonic()-start>sec:break
  u,v=line.split();A=(int(u,16)<<64)|int(v,16)
  if goal==96 and not(A&1):
   dest.write(json.dumps([idx,'endpoint'])+'\n');continue
  ass=([74] if goal==96 else [])
  for d in range(1,30,2):
   t=A&(A>>d)&(A>>(2*d));forbid=((t<<((d-1)//2))|(t>>((d+1)//2)))&((1<<(74-2*d))-1)
   while forbid:
    one=forbid&-forbid;forbid^=one;ass.append(activate[one.bit_length()-1,d])
  for i in range(1,74):
   ai=(A&((1<<i)-1)).bit_count()
   h=min(need,cap[2*i]-ai)
   lb=max(0,need-cap[148-2*i]+m-ai)
   if h<0 or lb>need:ass.append(False);break
   ass.extend([neg(prefix[i,h+1]),prefix[i,lb]])
  if any(x is False for x in ass):
   dest.write(json.dumps([idx,'prefix'])+'\n');continue
  solver.conf_budget(budget);res=solver.solve_limited(assumptions=[x for x in ass if x is not True])
  dest.write(json.dumps([idx,res])+'\n')
  if res:
   B=[x-1 for x in solver.get_model() if 1<=x<=74];W=sorted([2*x+1 for x in range(74) if A>>x&1]+[2*x+2 for x in B])
   assert len(W)==goal and all(not all(a+j*d in W for j in range(6)) for d in range(1,30) for a in range(1,149-5*d))
   print('FOUND',W,flush=True);(root/f'witness_{tag}.txt').write_text(str(W));break
