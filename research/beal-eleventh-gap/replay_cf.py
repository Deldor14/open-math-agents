"""Independent exact computation using continued fractions and modular residues."""
from fractions import Fraction
from math import factorial, gcd, isqrt

GAP = 1000
P_LIMIT = 200000
S = 2**672
ERR = 1024


def kth_root(n, k):
    if n == 0:
        return 0
    x = 1 << ((n.bit_length()+k-1)//k)
    while True:
        y = ((k-1)*x+n//x**(k-1))//k
        if y >= x:
            return x
        x = y


def small_exponent(p, last, moduli):
    # Bit j represents the odd gap 2*j+1. An equality must survive every modulus.
    width = (GAP+1)//2
    tables = {}
    for m in moduli:
        powers = {pow(v,p,m) for v in range(m)}
        table = []
        for residue in range(m):
            total = pow(residue,p,m)
            mask = 0
            for j in range(width):
                a = (total-2*j-1)*((m+1)//2) % m
                if (pow(a,11,m)+pow(total-a,11,m)) % m in powers:
                    mask |= 1 << j
            table.append(mask)
        tables[m] = table
    pairs = survivors = 0
    for u in range(3,last+1,2):
        if u%11 == 0:
            continue
        total = u**p
        allowed = min(width,(total-1)//2)
        mask = (1 << allowed)-1
        pairs += allowed
        for m in moduli:
            mask &= tables[m][u%m]
        while mask:
            bit = mask & -mask
            mask ^= bit
            h = 2*(bit.bit_length()-1)+1
            if gcd(h,u) == 1:
                a = (total-h)//2
                value = a**11 + (a+h)**11
                assert kth_root(value,p)**p != value, (u,h,p)
                survivors += 1
    return pairs, survivors


def convergents(n,d,bound):
    h0,h1,k0,k1 = 0,1,1,0
    while d:
        a,r = divmod(n,d)
        h0,h1 = h1,a*h1+h0
        k0,k1 = k1,a*k1+k0
        if k1 > bound:
            break
        yield h1,k1
        n,d = d,r


def verify():
    if not __debug__:
        raise RuntimeError("Assertions are required.")
    for p,limit,moduli in [(5,kth_root(1024*GAP**4,10),[11,31,41]),
                           (7,14*GAP-1,[29,43,71,113,127,197])]:
        print("p, pairs before modular filters, primitive survivors tested:", p,
              *small_exponent(p,limit,moduli))
    loglo = sum((Fraction(2,(2*i+1)*3**(2*i+1)) for i in range(240)),Fraction())
    L = int(S*loglo)
    assert L == int(S*(loglo+Fraction(3,3**481)))
    assert factorial(151)>S
    assert 4*ERR*(2*P_LIMIT*GAP)**20 < S
    assert 4*1023*GAP**2 < 13*101**6
    count = cf_count = tenth = checks = 0
    for p in range(13,P_LIMIT):
        if any(p%k == 0 for k in range(2,isqrt(p)+1)):
            continue
        count += 1
        h = 10*L//p
        assert 5*h < 3*S
        z = term = S
        for k in range(1,151):
            term = term*h//(S*k)
            z += term if k%2 == 0 else -term
            if term == 0:
                break
        candidates = []
        for n,q in convergents(z,S,(2*p*GAP)**10):
            cf_count += 1
            if q < 101**10 or isqrt(q)**2 != q:
                continue
            u = kth_root(q,10)
            if u**10 == q and u%2 and u%11:
                candidates.append((n,u))
                tenth += 1
        for u in range(3,101,2):
            if u%11 == 0:
                continue
            q = u**10
            den = p*u**(2*min(p,180))
            first = (q*(z-ERR)+S-1)//S
            last = (q*(z+ERR)*den+q*S*1023*GAP**2)//(S*den)
            candidates.extend((v,u) for v in range(first,last+1) if gcd(u,v)==1)
        for n,u in candidates:
            den = p*u**(2*min(p,180))
            q = u**10
            if S*n < q*(z-ERR) or (S*n-q*(z+ERR))*den > S*1023*GAP**2*q:
                continue
            checks += 1
            total = u**p
            target = (u*n)**p
            for gap in range(1,min(GAP,total-2)+1,2):
                if gcd(u,gap)==1:
                    a = (total-gap)//2
                    assert a**11+(a+gap)**11 != target, (a,gap,p)
    print("p>=13 checked / convergents / eligible large tenth powers / numerator checks:",
          count, cf_count, tenth, checks)
    print("Remaining primitive candidates: 0")


if __name__ == "__main__":
    verify()
