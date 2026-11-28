"""Compare the mixed exponent set with both independent class-number tables."""
from math import isqrt
from pathlib import Path

here = Path(__file__).resolve().parent
selected = set()
for folder, residues, expected_count in (
    ("inert-signatures", {2, 3, 4, 5}, 606),
    ("split-signatures", {1, 6}, 328),
):
    directory = here.parent / folder
    rows = [tuple(map(int, line.split()))
            for line in (directory / "bernoulli.txt").read_text().splitlines()]
    second = [tuple(map(int, line.split()))
              for line in (directory / "character-values.txt").read_text().splitlines()]
    assert rows == second
    assert [p for p, _, _ in rows] == [
        n for n in range(11, 20001) if n % 7 in residues
        and all(n % d for d in range(2, isqrt(n) + 1))
    ]
    group = {p for p, rational, twisted in rows if rational == twisted == 0}
    assert len(group) == expected_count and selected.isdisjoint(group)
    assert sorted(group) == list(map(int, (directory / "exponents.txt").read_text().split()))
    if folder == "split-signatures":
        split_proof = here.parent / "lambda-square" / "certificates.txt"
        assert sorted(group) == [int(line.split()[0]) for line in split_proof.read_text().splitlines()]
    selected.update(group)
assert sorted(selected) == list(map(int, (here / "exponents.txt").read_text().split()))
smooth = here.parent / "smooth" / "certificates.txt"
auxiliary = {int(row[0]): int(row[2]) for line in smooth.read_text().splitlines()
             for row in [line.split()]}
assert len(auxiliary) == 9547 and min(auxiliary.values()) > 100000
assert {11, 13, 17, 19, 23, 29} <= auxiliary.keys()
print(len(selected), "distinct exponents,", min(selected), "through", max(selected))
print(len(auxiliary), "auxiliary primes indexed by exponent, including the six small cases")
