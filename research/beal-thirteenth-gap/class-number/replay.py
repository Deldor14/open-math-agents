"""Construct and check principal generators, and write exact norm multiplicities."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import shutil
import subprocess
import tempfile

BOUND = 2**22
POLYNOMIAL = "x^21+2*x^14-16*x^7+8"


def run_gp(gp, code):
    result = subprocess.run([gp, "-qf", "-s", "512M"], input=code, text=True,
                            capture_output=True, check=True)
    if "***" in result.stderr:
        raise RuntimeError(result.stderr[-2000:])
    return result.stdout.splitlines()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("counts", type=Path)
    parser.add_argument("--gp", default="gp")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    gp = shutil.which(args.gp)
    if not gp or args.jobs < 1:
        parser.error("a PARI/GP executable and a positive worker count are required")
    routine = Path(__file__).with_name("principal.gp").read_text()
    with tempfile.TemporaryDirectory() as workdir:
        cache = Path(workdir) / "relations.bin"
        setup = f'''
P={POLYNOMIAL}; N=nfinit(P);
if(N.sign!=[3,9] || N.disc!=-(2^18*7^21*13^14),error("field invariants"));
B=bnfinit(N,1); writebin("{cache}",B); print("READY");
quit
'''
        if run_gp(gp, setup) != ["READY"]:
            raise RuntimeError("field or witness generator initialization failed")

        def block(first):
            last = min(first + 65535, BOUND-1)
            code = routine + f'\nB=read("{cache}"); verify_range(B,{first},{last},{BOUND});\nquit\n'
            rows = run_gp(gp, code)
            if not rows or rows[-1] != f"OK {len(rows)-1}":
                raise RuntimeError(f"incomplete prime range {first} to {last}")
            return Counter(map(int, rows[:-1]))

        counts = Counter()
        with ThreadPoolExecutor(max_workers=args.jobs) as workers:
            for partial in workers.map(block, range(2, BOUND, 65536)):
                counts.update(partial)
        args.counts.write_text("".join(f"{n} {counts[n]}\n" for n in sorted(counts)))
        print("verified principal ideals", sum(counts.values()))


if __name__ == "__main__":
    main()
