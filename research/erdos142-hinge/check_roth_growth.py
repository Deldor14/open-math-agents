"""Integer checks for the doubling and Fibonacci certificates."""
from itertools import combinations


def small_capacities(n):
    free_masks = [0]
    capacities = [0]
    for last in range(n):
        pairs = [(1 << (last - d)) | (1 << (last - 2*d))
                 for d in range(1, last//2 + 1)]
        free_masks.extend([s | (1 << last) for s in free_masks
                           if all(s & pair != pair for pair in pairs)])
        capacities.append(max(bin(s).count("1") for s in free_masks))
    return capacities


def check_gluing():
    cases = 0
    for a in range(1, 18):
        for b in range(1, a+1):
            left = set(range(a))
            right = set(range(2*a-1, 2*a+b-1))
            for x, y, z in combinations(sorted(left | right), 3):
                if x in left and z in right:
                    assert x+z != 2*y
            cases += 1
    return cases


def fibonacci(n):
    x, y = 0, 1
    for _ in range(n):
        x, y = y, x+y
    return x


def main():
    capacities = small_capacities(22)
    assert all(6*capacities[2*n] >= 7*capacities[n] for n in range(12))
    print("n=0,...,11: exact doubling passed")
    print("Separated interval pairs checked:", check_gluing())
    fib = [fibonacci(n) for n in range(173)]
    depth, m = 84, 171
    for step in range(depth):
        i = m-2*step
        assert 2*fib[i+1] > 3*fib[i] and fib[i+1] < 2*fib[i]
        assert 2*fib[i]-fib[i+1] == fib[i-2]
        assert fib[i+1]-fib[i] == fib[i-1]
    assert m-2*depth == 3
    q = fib[m] // (2*fib[3])
    # Max coordinate in the base-(2s-1) box is ((2s-1)^d-1)/2.
    s, dim = 109, 15
    assert ((2*s-1)**dim+1)//2 <= q
    layers = 1 + dim*(s-1)**2
    guaranteed = (s**dim + layers-1)//layers
    assert guaranteed > 2**depth
    print("q =", q)
    print("sphere-layer lower bound =", guaranteed, "> 2^84 =", 2**84)
    numerator, denominator = fib[m+1], fib[m]
    assert numerator**2-numerator*denominator-denominator**2 == -1
    print("lambda =", numerator, "/", denominator, "< golden ratio")


if __name__ == "__main__":
    main()
