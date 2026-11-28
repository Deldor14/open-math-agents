"""Verify all the digit inequalities of the 987/610 scalar countermodel.

The only tabulated inputs are seven upper bounds from Gasarch, Glenn,
and Kruskal, Finding Large 3-Free Sets I, Appendix II.
"""
STAGE = 7
M, W = 128, 987
BLOCKS = [(1, 1), (3, 2), (8, 4), (29, 11), (50, 16), (88, 24), (186, 40)]


def weights(s):
    out = [1, 3]
    while len(out) <= s:
        out.append(3 * out[-1] - out[-2])
    return out


def main():
    w = weights(STAGE)
    assert w[-1] == W and 1 << STAGE == M
    residues = [sum(w[t] for t in range(STAGE) if n & (1 << t)) for n in range(M)]

    def cap(n):
        whole, bits = divmod(n, M)
        return whole * W + residues[bits]

    assert cap(M - 1) + 1 == 610 and cap(M) == 987
    # Check the carry formula in the Lean file against all residues plus a period.
    for n in range(2 * M + 1):
        assert cap(n) == n + sum((w[t+1]-2*w[t])*(n >> (t+1)) for t in range(STAGE))
    assert all(v * M <= i * W for i, v in enumerate(residues))

    B, U = BLOCKS[-1]
    assert B == 186 and U == 40
    tail = 155
    threshold = tail + B
    assert U*W <= 2*M*B
    upper = [0] * threshold
    tests = 0
    direct = []
    for m in range(1, threshold):
        r = upper[m] = min(cost + upper[max(0, m-len_)] for len_, cost in BLOCKS)
        L = 2*m-1
        if W*r <= M*L:
            continue
        assert m < tail
        direct.append(m)
        for j in range(M):
            for residue in range(r):
                left = r * cap(r*j+residue)
                right = r * L * cap(j) + L * residue
                assert left <= right, (m, r, j, residue, left, right)
                tests += 1
    print('Directly tested moduli (m values):', len(direct))
    print('Largest m tested directly:', max(direct))
    print('Exact integer comparisons:', tests)
    print('Tail induction from', tail, 'uses the 186 consecutive starting values and R(186)<=40.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    main()
