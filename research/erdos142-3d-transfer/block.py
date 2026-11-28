"""Membership and rational height on the immutable growing-clip table."""
from fractions import Fraction as F
from pathlib import Path


def best_half(values):
    n = len(values)
    score = best = sum(values[:n//2])
    start = 0
    for j in range(1,n):
        score += values[(j+n//2-1)%n] - values[j-1]
        if score > best:
            best,start = score,j
    return best,start


def mask(a,b,n):
    if b-a >= n:
        return (1<<n)-1
    bits = ((1<<(b-a))-1) << (a%n)
    return (bits | bits>>n) & ((1<<n)-1)


def hinges(x,subdivisions):
    """Sum of (x-j/subdivisions)_+ over all unit-interval grid lines."""
    j = int(x*subdivisions)
    return (j+1)*x - F(j*(j+1),2*subdivisions)


def near_line(x,n,T):
    u = (x*n)%1
    return min(u,1-u)*T <= n


class Block:
    def __init__(self,source):
        lines = [list(map(int,line.split())) for line in Path(source).read_text().splitlines()]
        n,k = self.n,self.k = lines[0]
        assert n%2 == 0 and len(lines)==n+1
        self.birth = []
        self.parts = []
        for p,(j,b,length,*edges) in enumerate(lines[1:]):
            assert p==j and 0<=b<=k and 2*length==len(edges)
            self.birth.append(b)
            self.parts.append(list(zip(edges[::2],edges[1::2])))
        self.upper = [self.upper_column(p) for p in range(n)]
        self.primary = [best_half([col[h][2] for col in self.upper]) for h in range(k)]
        lower = sum((k-b)*sum(v-u for u,v in row) for b,row in zip(self.birth,self.parts))
        self.volume = F(2*lower+sum(count for count,start in self.primary),4*k*n*n)

    def upper_column(self,p):
        n,k = self.n,self.k
        born = [0]*k
        for total in (p,(p-1)%n):
            for i in range(n):
                j = (total-i)%n
                h = self.birth[i]+self.birth[j]
                if i>j or h>=k:
                    continue
                for a,b in self.parts[i]:
                    for c,d in self.parts[j]:
                        born[h] |= mask(a+c,b+d,n)
        valid = (1<<n)-1
        out = []
        for forbidden in born:
            now = valid & ~forbidden
            if not out or now!=valid:
                count,start = best_half([(now>>j)&1 for j in range(n)])
                kept = now & mask(start,start+n//2,n)
                assert bin(kept).count("1")==count
                record = (kept,start,count)
            out.append(record)
            valid = now
        return out

    def energy(self,z,s,t,T):
        n,k = self.n,self.k
        # Extra cuts at every j/(4k) also in the lower bands change area by O(1/T).
        if not (0<z<F(3,4)) or near_line(z,4*k,T):
            return None
        if z<F(1,2):
            x = s
            p = int(n*x)
            if self.birth[p]>int(2*k*z):
                return None
            signed = t if t<F(1,2) else t-1
            nt = n*signed
            if nt.denominator==1 or not any(a<nt<b for a,b in self.parts[p]):
                return None
            if x<F(1,2):
                Q = signed**2
            else:
                e = 2*signed-(F(1,2) if signed>0 else -F(1,2))
                Q = (1+e)**2
        else:
            h = int(4*k*(z-F(1,2)))
            ds,dt = (2*s)%1,(2*t)%1
            p = int(n*ds)
            x = (ds-F(self.primary[h][1],n))%1
            kept,start,count = self.upper[p][h]
            if x>=F(1,2) or (n*dt).denominator==1 or not (kept >> int(n*dt))&1:
                return None
            Q = ((dt-F(start,n))%1)**2
        if near_line(x,n,T):
            return None
        B = 16+8*(n+1)+3
        return 10*(B+1)*T*T*(z*z+hinges(z,4*k)) + 16*T*x*x+8*T*hinges(x,n)+Q

if __name__=='__main__':
    import argparse
    from transfer import construct
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('table');p.add_argument('--N',type=int)
    args=p.parse_args();block=Block(args.table)
    print('exact block volume',block.volume)
    if args.N is not None:
        print(construct(args.N,block))
