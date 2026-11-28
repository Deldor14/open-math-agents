"""List one-sided supports in the mixed septic equation; integer arithmetic only."""
from pathlib import Path

root = Path(__file__).resolve().parent
excluded = set(map(int, (root.parent / "mixed-seventh" / "exponents.txt").read_text().split()))
bound = 100000
primes = [2]
for n in range(3, bound + 3, 2):
    for d in primes:
        if d*d > n:
            primes.append(n)
            break
        if n % d == 0:
            break

def prime_factors(n):
    factors = set()
    for d in primes:
        if d*d > n:
            break
        if n % d == 0:
            factors.add(d)
            while n % d == 0:
                n //= d
    if n > 1:
        factors.add(n)
    return factors

def factors_of_order(r):
    if r == 7:
        return set()
    residue = r % 7
    if residue == 1:
        parts = [r-1]
    elif residue == 6:
        parts = [r+1]
    elif residue in (2,4):
        parts = [r-1, r*r+r+1]
    else:
        parts = [r+1, r*r-r+1]
    return {p for n in parts for p in prime_factors(n) if p >= 11}

if __name__ == "__main__":
    for r in primes:
        if r > bound:
            break
        missing = factors_of_order(r)
        if not missing:
            print(r, "local")
        elif missing <= excluded:
            print(r, "descent")
