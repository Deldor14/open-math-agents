"""Check the homogeneous profile inequalities needed for eight published affine digit rules."""
from fractions import Fraction

PERIOD = 128
WIDTH = 987
# modulus, gain numerator, gain denominator, terminal shortening
RULES = [(6,5,2,2),(13,9,2,4),(15,5,1,4),(17,11,2,1),(18,11,2,4),
         (19,6,1,8),(35,9,1,15),(37,10,1,1)]
WEIGHTS = [1,3,8,21,55,144,377]
RESIDUES = [sum(w for i,w in enumerate(WEIGHTS) if (j>>i)&1) for j in range(PERIOD)]

def capacity(j):
    periods,remainder=divmod(j,PERIOD)
    return periods*WIDTH+RESIDUES[remainder]

def right_inverse_value(level):
    integer=level.numerator//level.denominator
    return capacity(integer)+level-integer

def check_rule(modulus,numerator,denominator):
    r=Fraction(numerator,denominator)
    period=PERIOD*denominator
    # The right limit of p(ru)-L p(u) can be largest immediately after a
    # breakpoint at u=j or u=j/r; between breakpoints its slope is r-L<0.
    breaks={Fraction(j) for j in range(period)}
    breaks.update(Fraction(j,1)/r for j in range(PERIOD*numerator))
    for u in breaks:
        if right_inverse_value(r*u)>modulus*right_inverse_value(u):
            raise ValueError((modulus,r,u))
    # Different calculation, testing the inverse on the whole rational grid.
    for t in range(numerator*denominator*PERIOD):
        left=numerator*(denominator*capacity(t//denominator)+t%denominator)
        right=denominator*modulus*(numerator*capacity(t//numerator)+t%numerator)
        if left>right:raise ValueError((modulus,r,t))
    return len(breaks),numerator*denominator*PERIOD

if __name__=='__main__':
    totals=[0,0]
    for L,a,b,k in RULES:
        counts=check_rule(L,a,b)
        totals=[x+y for x,y in zip(totals,counts)]
        print(f'L={L}, gain={a}/{b}, shortening={k}, checks={counts}')
    print('total checks',totals)
