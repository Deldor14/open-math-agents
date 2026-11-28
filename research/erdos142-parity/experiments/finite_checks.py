"""Check the positive witnesses and the individual maximality claims in experiments.json."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
data = json.loads((ROOT / "experiments.json").read_text())


def progressions(n, k, strides):
    return [set(a + i*d for i in range(k))
            for d in strides for a in range(1, n - (k-1)*d + 1)]


for check in data["short_stride_hitting_sets"]:
    p, cap, points = check["p"], check["cap"], set(check["holes"])
    n = p * (p - 1) + 3
    assert points <= set(range(1, n + 1)) and len(points) <= p + 1
    assert max(sum(y % p == r for y in points) for r in range(p)) <= cap
    assert all(points & edge for edge in progressions(n, p, range(1, p)))

edges = progressions(148, 6, range(1, 30))
masks = data["reflection_symmetric_94_point_sets_hex"]
assert len(set(masks)) == len(masks)
for mask in masks:
    bits = int(mask, 16)
    points = {i + 1 for i in range(148) if (bits >> i) & 1}
    assert len(points) == 94 and points == {149 - x for x in points}
    assert {1,148} <= points and not any(edge <= points for edge in edges)
    for y in set(range(1,149)) - points:
        assert any((edge - points) == {y} for edge in edges)
print(f"Verified {len(masks)} locally maximal symmetric sets and {len(data['short_stride_hitting_sets'])} short-stride witnesses.")
