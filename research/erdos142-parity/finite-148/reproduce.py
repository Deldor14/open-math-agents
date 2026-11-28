"""Exhaust the cardinality-51 parity projection and retain unresolved cases."""
from pathlib import Path
from collections import Counter
import subprocess
import sys
import json

root = Path(__file__).resolve().parent
subprocess.run(['c++','-O3','-std=c++17','enumerate.cpp','-o','enumerate'],cwd=root,check=True)
masks = root/'51.hex'
with masks.open('w') as output:
    subprocess.run([str(root/'enumerate'),'6','74','51','0','0',str(root/'r6-through-147.txt')],cwd=root,stdout=output,check=True)
rows = masks.read_text().splitlines()
assert len(set(rows)) == len(rows) == 14706

def solve(filename, tag, conflicts):
    subprocess.run([sys.executable,'extend.py','51','96',str(conflicts),'21600',str(filename),tag],cwd=root,check=True)
    return [json.loads(line) for line in (root/f'parity_{tag}.jsonl').read_text().splitlines()]

for attempt,budget in enumerate([4500,100000,1000000]):
    if not rows:
        break
    current = root/f'input_{attempt}.hex'
    current.write_text(''.join(line+'\n' for line in rows))
    answers = solve(current, f'check_{attempt}', budget)
    assert len(answers) == len(rows)
    assert [n for n,_ in answers]==list(range(len(rows)))
    print('extension outcomes',Counter(answer for _,answer in answers))
    if any(answer is True for _,answer in answers):
        raise RuntimeError('a witness survived')
    assert all(answer in (False,None,'endpoint','prefix') for _,answer in answers)
    rows = [rows[n] for n,answer in answers if answer is None]
if rows:
    raise RuntimeError(f'{len(rows)} unresolved; no conclusion')
print('No size-51 parity class extends to a size-96 set.')
