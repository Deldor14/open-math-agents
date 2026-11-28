"""Certify inequalities for the golden Cantor profile by rational bounds on its inverse."""
import argparse
import math
from fractions import Fraction
from pathlib import Path

from verify_profile_archive import ARCHIVE_SHA256
import hashlib


SCALE = 10**24
ROOT = math.isqrt(5 * SCALE**2)
Z_LOW = Fraction(3 * SCALE - ROOT - 1, 2 * SCALE)
Z_HIGH = Fraction(3 * SCALE - ROOT, 2 * SCALE)


def inverse_bounds(t, depth):
    """Bound the binary digits of t read with powers of z=(3-sqrt(5))/2, for 0<=t<=1."""
    if not 0 <= t <= 1:
        raise ValueError("Expected a level between zero and one.")
    whole, fraction = divmod(t, 1)
    lower = upper = Fraction(whole)
    lo_power = hi_power = Fraction(1)
    for _ in range(depth):
        if not fraction:
            return lower, upper
        bit, fraction = divmod(2 * fraction, 1)
        lo_power *= Z_LOW
        hi_power *= Z_HIGH
        if bit:
            lower += lo_power
            upper += hi_power
    if fraction:
        upper += hi_power * Z_HIGH / (1 - Z_HIGH)
    return lower, upper


def classify(gain, length):
    for depth in range(0, 113, 4):
        lo, hi = inverse_bounds(1 / Fraction(gain), depth)
        if length * lo >= 1:
            return True, depth
        if length * hi < 1:
            return False, depth
    raise ArithmeticError("This precision did not decide the inequality.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    data = args.archive.read_bytes()
    assert hashlib.sha256(data).hexdigest() == ARCHIVE_SHA256
    records = [tuple(map(int, line.split()[:2])) for line in data.splitlines() if line.strip()]
    checked = [classify(r, l) for r, l in records]
    assert len(records) == 1024 and all(passed for passed, _ in checked)
    print("Archive checked:", len(checked), "largest bit cutoff:", max(k for _, k in checked))
    r, length = 2303115151489024, 59**3 * 61**9
    assert not classify(r, length)[0]
    lo, hi = inverse_bounds(Fraction(1, r), 80)
    assert Fraction(7114, 10000) < length * lo <= length * hi < Fraction(7115, 10000)
    print("Mixed-radix sphere: 0.7114 < L P(1/r) < 0.7115.")


if __name__ == "__main__":
    main()
