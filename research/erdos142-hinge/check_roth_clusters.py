"""Independent finite checks of cluster shapes, phase choices, and matching directions."""
from itertools import combinations


def free(S):
    return all(x + z != 2*y for x,y,z in combinations(sorted(S),3))


def weak(S, targets):
    return all(abs(x+y+z-3*c) not in targets
               for x,y,z in combinations(S,3) for c in (x,y,z))


def optimum(S):
    sites = sorted(S)
    for size in reversed(range(len(sites)+1)):
        for choice in combinations(sites,size):
            if free(choice):
                return choice


def components(S, steps):
    unseen = set(S)
    while unseen:
        root = min(unseen)
        part = {root}
        queue = [root]
        unseen.remove(root)
        while queue:
            x = queue.pop()
            for d in steps:
                for y in (x-d,x+d):
                    if y in unseen:
                        unseen.remove(y)
                        part.add(y)
                        queue.append(y)
        yield sorted(part)


def enumerate_shapes(targets, steps):
    shapes = {(0,)}
    new = [(0,)]
    while new:
        old = new.pop()
        for x in sorted({i+s*d for i in old for d in steps for s in (-1,1)}-set(old)):
            if x < 0:
                continue
            candidate = tuple(sorted(old+(x,)))
            if candidate not in shapes and weak(candidate, targets):
                shapes.add(candidate)
                new.append(candidate)
    return sorted(shapes)


ONE = [(0,), (0,1), (0,2), (0,1,3), (0,2,3), (0,2,3,5)]
TWO = [(0,), (0,1), (0,2), (0,4), (0,1,5), (0,4,5), (0,4,5,9)]


def outputs(shape,p,q,width,h):
    stop = (p*max(shape)+h+width+q-1)//q
    return {u for j in shape for u in range(stop)
            if (u-j)%2==0 and p*j+h<=q*u<p*j+h+width}


def finite_tables():
    assert enumerate_shapes({0,2}, (1,2)) == sorted(ONE)
    assert enumerate_shapes({0,2,4}, (1,2,4)) == sorted(TWO)
    for c in TWO:
        for h in range(10):
            assert len(optimum(outputs(c,4,5,12,h)))>=len(c)
    for c in ONE:
        v = [len(optimum(outputs(c,2,1,4,h))) for h in range(2)]
        assert sum(v)>=3*len(c)
    print('Normalized patterns (one / two defects):',len(ONE),len(TWO))
    print('Finite phase cases (compression / single-defect doubling):',70,12)


def test_intervals():
    family = [()]
    for b in range(12):
        family += [S+(b,) for S in family if free(S+(b,))]
    extent = lambda A: A[-1]+1 if A else 1
    measurements = 0
    for A in family:
        n = extent(A)
        for t in range(1,7):
            if not weak(A,{0,t,2*t}):
                continue
            unions = set(A) | {a+t for a in A}
            P = sum(a+t in A for a in A)
            assert 3*len(optimum(unions))+2*P >= 4*len(A)
            # Use the same zero phase in every component, with exact inequalities.
            windows = {y for a in A for y in range((4*(n-1)+6*t+4)//5)
                       if (y-a)%t == 0 and 4*a<=5*y<4*a+6*t}
            assert len(optimum(windows))>=len(A)
            measurements += 1
    print('Actual interval gains and compressions:', measurements)


def digit_sums(weights, alphabet):
    sums = {0}
    for weight in weights:
        sums = {total + digit*weight for total in sums for digit in alphabet}
    return sums


def check_orbits(points, directions):
    binary = digit_sums(directions, (0,1))
    ternary = digit_sums(directions, (0,1,2))
    assert len(binary) == 2**len(directions)
    assert len(ternary) == 3**len(directions)
    remaining = set(points)
    expanded = set()
    anchors = 0
    while remaining:
        anchor = min(remaining)
        cube = {anchor + digit for digit in binary}
        assert cube <= remaining
        remaining -= cube
        enlargement = {anchor + digit for digit in ternary}
        assert expanded.isdisjoint(enlargement)
        expanded.update(enlargement)
        anchors += 1
    assert len(expanded) == anchors * 3**len(directions)
    assert max(expanded) <= max(points) + sum(directions)
    return anchors


def test_directions():
    family = [()]
    for b in range(14):
        family += [S+(b,) for S in family if free(S+(b,))]
    graphs = exact = several = 0
    for A in family[1:]:
        pts = set(A)
        directions = range(1, max(A)+1)
        unmatched = lambda d: sum(a-d not in pts and a+d not in pts for a in A)
        perfect = [d for d in directions if unmatched(d)==0]
        for dimension in range(len(perfect)+1):
            for weights in combinations(perfect, dimension):
                anchors = check_orbits(pts, weights)
                exact += 1
                if dimension >= 2 and anchors >= 2:
                    several += 1
        for d,e in combinations(directions,2):
            away = 0
            for C in components(A,(d,e)):
                assert len(C)<=4
                square = len(C)==4 and set(C)=={C[0],C[0]+d,C[0]+e,C[0]+d+e}
                if not square:
                    away += len(C)
            assert away<=2*(unmatched(d)+unmatched(e))
            graphs += 1
    assert several > 0
    print('Two-direction graphs and exact-tiling tests:', graphs, exact)
    print('Multiple anchors with at least two common directions:', several)


def test_approximate_orbits():
    # Seven base-three places give many disjoint cubes on the first few places.
    large_cube = digit_sums([3**j for j in range(7)], (0,1))
    cases = 0
    for holes in ((0,), (0,4), (1,3,9), (27,81)):
        points = large_cube - set(holes)
        for weights in ((1,3), (3,9), (1,3,9), (1,9,27)):
            missing = {d: {x for x in points if x-d not in points and x+d not in points}
                       for d in weights}
            good = points - set.union(*missing.values())
            for d,e in combinations(weights,2):
                squares = [s for s in components(points,(d,e)) if
                           set(s) == {s[0],s[0]+d,s[0]+e,s[0]+d+e}]
                good &= {x for s in squares for x in s}
            starts = set(good)
            for d in reversed(weights):
                def move(x):
                    if x+d in points:
                        return x+d
                    return x-d if x-d in points else x
                starts = {x for x in starts if move(x) in starts}
            dimension = len(weights)
            misses = sum(map(len, missing.values()))
            assert len(points)-len(starts) <= 2**dimension * (2*dimension-1) * misses
            assert starts and misses
            cubical = set()
            for orbit in components(points,weights):
                if starts.intersection(orbit):
                    assert check_orbits(set(orbit),weights) == 1
                    cubical.update(orbit)
            assert starts <= cubical
            check_orbits(cubical,weights)
            cases += 1
    print('Almost-perfect direction families with missing vertices:', cases)


if __name__=='__main__':
    finite_tables()
    test_intervals()
    test_directions()
    test_approximate_orbits()
