"""Independently recover primitive short models directly from minimal c4,c6."""
from collections import defaultdict
from math import gcd, isqrt
from pathlib import Path
import sys


def verify(file, counts_file):
    groups = {}
    for line in counts_file.read_text().splitlines():
        if line.startswith('# S = {'):
            places, count = line[7:].split('}: ')
            groups[tuple(map(int, places.split(', ')))] = int(count)
    expected = {p for p in range(3,164,2) if all(p%i for i in range(2,isqrt(p)+1))}
    found_groups = set()
    answers = set()
    counts = defaultdict(int)
    p = 0
    for line in file.read_text().splitlines():
        if line.startswith('# S = {'):
            places = tuple(map(int,line[7:-2].split(', ')))
            p = 0
            if places == (2,3) or (len(places)==3 and places[:2]==(2,3) and places[2] in expected):
                p = places[-1]
                found_groups.add(p)
        elif p and line.startswith('('):
            counts[places] += 1
            c4,c6 = map(int,line[1:-1].split(','))
            for scale in (1,2):
                v,rest_v = divmod(-c4*scale**4,144)
                u,rest_u = divmod(abs(c6)*scale**6,1728)
                if rest_v or rest_u or min(u,v)<1 or gcd(u,v)>1:
                    continue
                n = u*u + v**3
                pk,k = p**3,3
                while pk < n:
                    pk *= p
                    k += 1
                if n == pk:
                    answers.add((p,k,u,v))
    assert found_groups == expected
    assert all(n==groups[s] for s,n in counts.items())
    return sorted(answers)


if __name__=='__main__':
    for solution in verify(Path(sys.argv[1]),Path(sys.argv[2])):
        print(*solution)
