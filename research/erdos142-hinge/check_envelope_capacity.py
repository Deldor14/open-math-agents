"""Independent checks of the two-arc capacity formula using integer-scaled geometry."""
from itertools import product


def intersection_length(left, right, low, high):
    return max(0, min(right, high) - max(left, low))


def reflected_length(arcs, v, period):
    return sum(
        intersection_length(a, b, v - d + k * period, v - c + k * period)
        for a, b in arcs for c, d in arcs for k in (-1, 0, 1, 2)
    )


def check_mesh(half_period):
    # Even endpoints retain all half-integral cuts on this mesh.
    h = half_period
    count = 0
    for b, c, d in product(range(0, h + 1, 2), repeat=3):
        if c > d:
            continue
        arcs = [(h, h + b), (c, d)]
        ends = [value for arc in arcs for value in arc]
        vertices = {(x + y) % (2 * h) for x in ends for y in ends}
        min_reflection = min(reflected_length(arcs, v, 2 * h) for v in vertices)
        left = max(0, (b + d - h) // 2)
        right = (h + c) // 2
        choices = [
            ((0, b), (c, c)),
            ((0, min(b, c)), (c, d)),
            ((left, b), (max(c, left), d)),
            ((0, min(b, right)), (c, min(d, right))),
        ]
        best = 0
        for (i, j), (k, l) in choices:
            assert 0 <= i <= j <= b and c <= k <= l <= d
            local = (j + l - 2 * min(i, k) <= h or 2 * max(j, l) - i - k <= h
                     or j <= k or l <= i or i == j or k == l)
            assert local
            best = max(best, j - i + l - k)
        assert 2 * (b + d - c - best) == min_reflection
        count += 1
    return count


if __name__ == "__main__":
    print(f"{check_mesh(48)} exact envelope checks passed")
