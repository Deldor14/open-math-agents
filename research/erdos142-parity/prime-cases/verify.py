"""Rebuild each CNF, check both constructions, and replay the DRAT proof."""
import argparse
import hashlib
import json
import lzma
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def progressions(k, n):
    for stride in range(1, (n - 1) // (k - 1) + 1):
        for start in range(1, n - (k - 1) * stride + 1):
            yield [start + i * stride for i in range(k)]


def check_construction(p, n, extras):
    holes = {j * p for j in range(1, p)} | set(range(1, extras + 1))
    assert len(holes) == p - 1 + extras
    for progression in progressions(p, n):
        if holes.isdisjoint(progression):
            raise ValueError(f"Unhit progression in [1,{n}]: {progression}")


def negate(value):
    return not value if isinstance(value, bool) else -value


def make_cnf(k, n, budget):
    clauses = list(progressions(k, n))
    largest_var = n

    def add_clause(*literals):
        if not any(x is True for x in literals):
            clauses.append([x for x in literals if x is not False])

    for stride in range(1, (n - 1) // (k - 1) + 2):
        rows = [range(start, n + 1, stride) for start in range(1, stride + 1)]
        minimum = sum(len(row) // k for row in rows)
        for row in rows:
            length = len(row)
            cap = budget - minimum + length // k
            if cap < 0:
                return largest_var, clauses + [[]]
            if cap >= length and stride > 1:
                continue
            low = [i // k for i in range(length + 1)]
            high = [min(i, cap - (length - i) // k) for i in range(length + 1)]
            if any(x > y for x, y in zip(low, high)):
                return largest_var, clauses + [[]]
            counters = []
            for i in range(length + 1):
                current = {}
                for j in range(low[i] + 1, high[i] + 1):
                    largest_var += 1
                    current[j] = largest_var
                counters.append(current)

            def at_least(prefix, count):
                if count <= low[prefix]:
                    return True
                if count > high[prefix]:
                    return False
                return counters[prefix][count]

            for i, point in enumerate(row, 1):
                for j in range(max(1, low[i - 1]), high[i - 1] + 3):
                    prev = at_least(i - 1, j)
                    one_less = at_least(i - 1, j - 1)
                    cur = at_least(i, j)
                    add_clause(negate(prev), cur)
                    add_clause(negate(one_less), -point, cur)
                    add_clause(negate(cur), prev, point)
                    add_clause(negate(cur), one_less)

            for i in range(length + 1):
                for j in range(i + k, length + 1, k):
                    bound = (j - i) // k
                    for count in range(low[i], high[i] + 1):
                        add_clause(negate(at_least(i, count)), at_least(j, count + bound))

    return largest_var, clauses


def write_cnf(p, n, path):
    nvars, clauses = make_cnf(p, n, p + 1)
    with path.open("w", newline="\n") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(map(str, clause)) + " 0\n")


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", nargs="*", type=int)
    parser.add_argument("--drat-trim", default="drat-trim")
    parser.add_argument("--cnf-only", action="store_true", help="only validate witnesses and CNF hashes")
    parser.add_argument("--raw", type=Path, help="directory containing original .drat files")
    args = parser.parse_args()
    cases = {row["p"]: row for row in json.loads((ROOT / "cases.json").read_text())}
    for p in args.primes or cases:
        row = cases[p]
        n = p * (p - 1) + 3
        assert row["n"] == n and row["r"] == n - p - 2
        check_construction(p, n - 1, 2)
        check_construction(p, n, 3)
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            cnf = work / "case.cnf"
            write_cnf(p, n, cnf)
            if sha256(cnf) != row["cnf_sha256"]:
                raise ValueError(f"CNF hash mismatch for p={p}")
            if args.cnf_only:
                print(f"p={p}: witnesses and CNF match", flush=True)
                continue
            if args.raw:
                proof = args.raw / f"hit{p}_{n}_{p+1}.drat"
                if sha256(proof) != row["drat_sha256"]:
                    raise ValueError(f"Original proof hash mismatch for p={p}")
                flags = ["-i"] if row.get("raw_binary") else []
            else:
                compressed = ROOT / "proofs" / f"p{p}.bdrat.xz"
                if sha256(compressed) != row["compressed_sha256"]:
                    raise ValueError(f"Compressed proof hash mismatch for p={p}")
                proof = work / "case.bdrat"
                with lzma.open(compressed, "rb") as source, proof.open("wb") as dest:
                    shutil.copyfileobj(source, dest)
                flags = ["-i"]
            result = subprocess.run([args.drat_trim, str(cnf), str(proof), *flags],
                                    capture_output=True, text=True, check=True)
            if "s VERIFIED" not in result.stdout.splitlines():
                raise ValueError(f"No verification verdict for p={p}")
            print(f"p={p}, N={n}: r_p(N)={row['r']}, DRAT verified", flush=True)


if __name__ == "__main__":
    main()
