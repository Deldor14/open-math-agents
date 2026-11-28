"""Finite checks of conditional root gains and generic arithmetic tree embeddings."""
from itertools import combinations, product


def tree_data(k, anchors):
    children = {}
    depths = [0]
    edges = []
    for anchor in anchors:
        fresh = tuple(range(len(depths), len(depths)+k-1))
        depths.extend([depths[anchor]+1]*(k-1))
        children.setdefault(anchor, []).append(fresh)
        edges.append((anchor,)+fresh)
    return edges, children, depths


def check_boundary(k, anchors):
    edges, children, depths = tree_data(k, anchors)
    boundary = [i for i, depth in enumerate(depths) if depth == max(depths)]
    edge_masks = [sum(1 << i for i in e) for e in edges]
    scores = {}
    for mask in range(1 << len(depths)):
        if any(mask & e == e for e in edge_masks):
            continue
        pattern = tuple((mask >> i) & 1 for i in boundary)
        key = (pattern, mask & 1)
        scores[key] = max(scores.get(key, -1), bin(mask).count('1'))

    def message(vertex, forced):
        if vertex in forced:
            return forced[vertex]
        return int(not any(all(message(i, forced) for i in edge)
                           for edge in children.get(vertex, [])))

    extremes = [message(0, dict.fromkeys(boundary, b)) for b in (0, 1)]
    checked = 0
    for states in product((-1,0,1), repeat=len(boundary)):
        forced = {i:s for i,s in zip(boundary, states) if s >= 0}
        # Unfixed boundary vertices are leaves and available to the optimum.
        messages = {i:forced.get(i,1) for i in boundary}
        optimum = [-1,-1]
        for (pattern, root), size in scores.items():
            if all(s < 0 or v == s for s,v in zip(states,pattern)):
                optimum[root] = max(optimum[root], size)
        assert optimum[0] >= 0
        gain = max(optimum)-optimum[0]
        assert min(extremes) <= gain == message(0, messages) <= max(extremes)
        checked += 1
    return checked


def check_generic(k, anchors):
    edges, _, _ = tree_data(k, anchors)
    intended = {tuple(sorted(e)) for e in edges}
    checks = 0
    for slots in product(range(k), repeat=len(edges)):
        points = [(0,)*len(edges)]
        for index, (edge, slot) in enumerate(zip(edges, slots)):
            base = points[edge[0]]
            for step in range(-slot,k-slot):
                if step:
                    row = list(base)
                    row[index] += step
                    points.append(tuple(row))
        assert len(points)==len(set(points))
        found = set()
        for group in combinations(range(len(points)), k):
            # A nonconstant vector progression is sorted lexicographically in one direction.
            ordered = sorted(points[i] for i in group)
            if all(a+c==2*b for row in zip(*ordered) for a,b,c in zip(row,row[1:],row[2:])):
                found.add(group)
        assert found == intended
        checks += 1
    return checks


if __name__ == '__main__':
    shapes = [(3,(0,)),(3,(0,0)),(3,(0,1)),(3,(0,1,2)),
              (3,(0,0,1,4)),(3,(0,1,3,5)),(4,(0,1)),(4,(0,0))]
    print('Boundary assignments:', sum(check_boundary(k,a) for k,a in shapes))
    print('Generic attachment configurations:', sum(check_generic(k,a) for k,a in shapes))
