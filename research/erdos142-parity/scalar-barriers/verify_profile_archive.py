"""Check the Fibonacci profile against the parameters in Wróblewski's BESTMOD.TXT."""
import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

WEIGHTS = (1, 3, 8, 21, 55, 144, 377, 987)
PERIOD = 1 << (len(WEIGHTS) - 1)
ARCHIVE_SHA256 = "686deba4b2e9a89397210f51caaef931f1607fd8eb8d9677fe2ab4c64cdf66e2"


def capacity(level):
    periods, remainder = divmod(level, PERIOD)
    return periods * WEIGHTS[-1] + sum(
        weight for bit, weight in enumerate(WEIGHTS[:-1]) if remainder & (1 << bit)
    )


def upper_inverse(level):
    whole, fraction = divmod(level, 1)
    return capacity(int(whole)) + fraction


def needed_dilation(gain):
    return max(
        Fraction(weight) / upper_inverse(Fraction(1 << bit) / gain)
        for bit, weight in enumerate(WEIGHTS)
    )


def compare_grid(gain):
    # At integer gain the earlier exact period test uses t=1,...,128*gain.
    limit = needed_dilation(gain)
    maximum = max(
        Fraction(capacity(t) * gain, gain * capacity(t // gain) + t % gain)
        for t in range(1, PERIOD * gain + 1)
    )
    assert limit == maximum


def all_depths(gain, modulus):
    # Fibonacci weights satisfy w[k+2]=3w[k+1]-w[k].
    weights = [1, 3]
    for depth in range(100):
        while len(weights) <= depth + 1:
            weights.append(3 * weights[-1] - weights[-2])
        level = Fraction(1 << depth) / gain
        whole = int(level)
        set_bits = [bit for bit in range(whole.bit_length()) if whole & (1 << bit)]
        value = sum(weights[bit] for bit in set_bits)
        if weights[depth] > modulus * (value + level - whole):
            return False, depth
        margin = modulus * value - weights[depth]
        next_margin = modulus * sum(weights[bit + 1] for bit in set_bits) - weights[depth + 1]
        if 0 <= margin <= next_margin:
            return True, depth
    raise ArithmeticError("No tail certificate within 100 levels.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="local copy of the primary BESTMOD.TXT")
    args = parser.parse_args()
    data = args.archive.read_bytes()
    if hashlib.sha256(data).hexdigest() != ARCHIVE_SHA256:
        raise ValueError("Archive version differs from the one used in the manuscript.")
    records = [tuple(map(int, line.split()[:2])) for line in data.splitlines() if line.strip()]
    assert [r for r, _ in records] == list(range(1, 1025))
    certified_depths = []
    for r, modulus in records:
        threshold = needed_dilation(Fraction(r))
        assert modulus >= threshold, (r, modulus, threshold)
        passes, depth = all_depths(r, modulus)
        assert passes, (r, modulus, depth)
        certified_depths.append(depth)
        if r > PERIOD // 2:
            assert threshold == Fraction(WEIGHTS[-1] * r, PERIOD)
    for gain, modulus in [(Fraction(5, 2), 6), (Fraction(9, 2), 13),
                          (Fraction(11, 2), 17), (Fraction(11, 2), 18),
                          (5, 15), (6, 19), (9, 35), (10, 37), (161, 2679)]:
        assert all_depths(gain, modulus)[0]
    assert all_depths(2303115151489024, 59**3 * 61**9) == (False, 51)
    print("All depths certified. Largest tail starting index:", max(certified_depths))
    for gain in range(1, PERIOD // 2 + 1):
        compare_grid(gain)
    ranked = sorted((Fraction(modulus) / needed_dilation(r), r, modulus)
                    for r, modulus in records if r >= 3)
    print(f"{len(records)} archived pairs passed. First three by relative margin:")
    for ratio, r, modulus in ranked[:3]:
        print(f"r={r}  archive={modulus}  threshold={needed_dilation(r)}  ratio={ratio}")
    print("Independent complete-period comparison for integer gains 1 through 64 passed.")


if __name__ == "__main__":
    main()
