"""Check each principal-ideal witness by its norm and its residue."""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from json import dumps
from pathlib import Path
import subprocess

parser = ArgumentParser()
parser.add_argument("gp", type=Path)
parser.add_argument("relations", type=Path)
parser.add_argument("factor_counts", type=Path)
parser.add_argument("--jobs", type=int, default=2)
args = parser.parse_args()
source = Path(__file__).with_suffix(".gp").read_text()
T = 2**22
width = 65536


def block(first):
    last = min(T-1, first+width-1)
    command = source + (
        f'\nB=read({dumps(str(args.relations.resolve()), ensure_ascii=False)}); '
        f'iferr(check_principal_norms(B,{first},{last}),E,print(E);quit(1));\nquit\n'
    )
    p = subprocess.run([str(args.gp.resolve()), "-qf", "-s", "256M"],
                       input=command, capture_output=True, text=True, check=True)
    rows = p.stdout.splitlines()
    if p.stderr or not rows or rows[-1] != f"count {len(rows)-1}":
        raise ValueError((first,last,p.stderr,rows[-2:]))
    return Counter(map(int,rows[:-1]))


if __name__ == "__main__":
    expected = Counter()
    for line in args.factor_counts.read_text().splitlines():
        n,k = map(int,line.split())
        expected[n] += k
    result = Counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for chunk,data in enumerate(pool.map(block,range(2,T,width)),1):
            result.update(data)
            if chunk%16 == 0:
                print("Blocks complete:",chunk,"ideals:",sum(result.values()),flush=True)
    if result != expected:
        raise ValueError("The counts by norm differ from the polynomial factorization.")
    print("Exact residue and norm checks:",sum(result.values()))
    print("Distinct ideal norms:",len(result))
