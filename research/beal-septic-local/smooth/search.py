"""Find auxiliary primes exceeding the smoothness bound for each candidate p."""
from pathlib import Path
from math import gcd,isqrt
import subprocess,sys
from resonance import factors,primes_to


def probable(n):
    if n<2 or any(n%r==0 for r in (2,3,5,7,11,13,17,19,23,29)):
        return n in (2,3,5,7,11,13,17,19,23,29)
    d=n-1; s=0
    while d%2==0:
        d//=2;s+=1
    for a in (2,3,5,7,11,13,17):
        x=pow(a,d,n)
        if x==1 or x==n-1:
            continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1:
                break
        else:
            return False
    return True


def candidate(p,q):
    m=(q-1)//p
    small=primes_to(isqrt(m)+2)
    divisors=set(factors(m,small))|{p}
    g=next(g for g in range(2,q) if all(pow(g,(q-1)//r,q)!=1 for r in divisors))
    z=[pow(g,(q-1)//7*i,q) for i in range(1,7)]
    h=1; step=pow(g,p,q)
    cases={-z[0]%q,-z[-1]%q}
    for _ in range(m):
        if h!=1:
            cases.add((z[0]-h*z[-1])*pow(h-1,-1,q)%q)
        h=h*step%q
    for t in cases-{0,q-1}:
        if p<=20000:
            den=pow(t+1,m,q)
            if any((v:=(t+r)%q) and pow(v,m,q)!=den for r in z):
                continue
        else:
            w=[(t+r)%q for r in z]
            if any(a and b and pow(a,m,q)!=pow(b,m,q) for a,b in zip(w[:3],w[::-1])):
                continue
            if (pow(t,7,q)+1)%q and pow((pow(t,7,q)+1)*pow(t+1,-7,q)%q,m,q)!=1:
                continue
        return False
    return True


def main():
    bound=int(sys.argv[1]); exps=Path(sys.argv[2]); gp=sys.argv[3]
    existing={p:(q,a,b) for p,q,a,b in (map(int,s.split()) for s in Path(sys.argv[4]).read_text().splitlines())}
    with subprocess.Popen([gp,'-fq'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as proc:
        proc.stdin.write('E=ellinit([0,-1,0,-2,1]);F=ellinit([0,-4,0,-11,43]);\n')
        proc.stdin.write('has3(a,b,c,q)={my(f=3*x^4+4*a*x^3+6*b*x^2+12*c*x+4*a*c-b^2,v=polrootsmod(f,q));for(i=1,#v,if(kronecker(lift(((v[i]+a)*v[i]+b)*v[i]+c),q)==1,return(1)));0};\n')
        for p in map(int,exps.read_text().split()):
            if p in existing and existing[p][0]>bound:
                print(p,'table',*existing[p],flush=True);continue
            k=max(1,(bound-1)//(14*p)+1)
            while True:
                q=14*p*k+1;k+=1
                if not probable(q) or not candidate(p,q):
                    continue
                if p*p>16*q:
                    mode='three'
                    line=f'print(has3(-1,-2,1,{q})," ",has3(-4,-11,43,{q}))'
                else:
                    mode='trace'
                    line=f'print(ellap(E,{q})," ",ellap(F,{q}))'
                proc.stdin.write(line+'\n');proc.stdin.flush()
                a,b=map(int,proc.stdout.readline().split())
                if (a-b)%p:
                    print(p,mode,q,a,b,flush=True);break
        proc.stdin.close()


if __name__=='__main__':main()
