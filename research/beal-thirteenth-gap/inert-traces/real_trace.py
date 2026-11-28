"""Exact traces in the maximal real subfield of a prime cyclotomic field."""
def real_traces(ell):
    def element(terms):
        v = [0]*ell
        for exponent, coefficient in terms:
            v[exponent % ell] += coefficient
        return v

    def product(a, b):
        return element((i+j, u*v) for i,u in enumerate(a) for j,v in enumerate(b))

    def coordinate(j):
        return element([(j,1),(-j,1)])

    x = coordinate(1)
    # x=z^-1(1+z^2); the inverse of (1+z^2) is minus the sum
    # of the odd powers of z^2 up to exponent ell-2 in that variable.
    inv = element((1+2*j,-1) for j in range(1,ell-1,2))
    unit = product(x, inv)
    unit[0] -= 1
    assert len(set(unit)) == 1  # zero modulo Phi_ell
    inv2 = product(inv,inv)
    inv3 = product(inv2,inv)
    factor = [a+3*b+2*c for a,b,c in zip(inv,inv2,inv3)]
    rows = []
    for j in range(1,(ell+1)//2):
        xj = coordinate(j)
        w = [a-2*b for a,b in zip(product(xj,xj),xj)]
        value = product(w,factor)
        assert all(value[k] == value[-k] for k in range(ell))
        full_trace = ell*value[0]-sum(value)
        assert full_trace % 2 == 0
        rows.append(full_trace//2)
    return rows


def order_up_to_sign(a, ell):
    v = a % ell
    order = 1
    while v not in (1,ell-1):
        v = v*a % ell
        order += 1
    return order


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O.")
    values = real_traces(13)
    assert values == [-91,1521,416,-52,-195,1053]
    inert = [j for j in range(1,7) if order_up_to_sign(j,13)==6]
    assert inert == [2,6]
    assert values[1]==3**2*13**2 and values[5]==3**4*13
    assert order_up_to_sign(3,13) < 6
    print("Exact relative-chord traces:",values)
    print("Inert classes up to sign:",inert)
    print("Trace for p=11:",values[1] % 11)
