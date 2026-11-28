"""Finite checks for the proof at the exponent prime. Python 3, stdlib."""
from math import comb

indices = {1, 2, 3}
for residue in range(1, 7):
    stable = set(indices)
    for _ in range(6):
        stable = {residue*j % 7 for j in stable} & indices
    assert len(stable) == (3 if residue == 1 else 0)
    print('p mod 7', residue, 'reference p-rank', len(stable))

p = 29
affine = sum((y*y-x**7-1) % p == 0 for x in range(p) for y in range(p))
trace = p+1-(affine+1)
diagonal = [comb((p-1)//2, j*(p-1)//7) % p for j in (1,2,3)]
assert affine+1 == 24 and trace == 6
assert sum(diagonal) % p == trace and diagonal == [15,16,4]
assert all((trace-s) % p for s in (-3,-1,1,3))
print('p=29', 'points',affine+1, 'trace',trace, 'Cartier diagonal',diagonal)
