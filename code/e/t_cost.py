import os
# Cost of the provable routine: blocks vs the proven bound, ops / y^(1/3), uniformity in L,
# and comparison with the hull-walk steps of REPORT_M2dv.md.
import sys, random, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'e'))
import blocksum as B
from math import isqrt, log, log2
random.seed(5)

def bound_blocks(y, L):
    c = y ** (1.0 / 3)
    r = isqrt(y)
    N1 = max(L + 1, B.icbrt(y) + 1)
    if N1 > r: return 0
    return 1 + (4 * c + 1) * log(r / N1) + log2(y ** (1 / 6.0)) + 1

print("%-8s %-7s %8s %10s %8s %8s %9s %9s" % ("y", "L", "blocks", "bound", "bl/y3", "ops/y3", "ops/y3ln2", "evals/bl"))
for e in (6, 8, 10, 12, 14, 16, 18):
    y = 10 ** e + random.randint(0, 10 ** (e - 1))
    r = isqrt(y); c3 = y ** (1 / 3.0)
    Ls = [0, int(c3), int(y ** 0.4), int(y ** 0.45), int(y ** 0.49)]
    if e >= 16: Ls = [0, int(y ** 0.45), int(y ** 0.49)]
    for L in Ls:
        ct = B.Ctr()
        v = B.S(y, L, ct)
        if e <= 12:
            assert v == B.S_brute(y, L)
        bb = bound_blocks(y, L)
        assert ct.blocks <= bb
        print("1e%-6d %-7s %8d %10.0f %8.3f %8.2f %9.4f %9.1f" % (e, "y^%.2f" % (log(L) / log(y)) if L > 0 else "0",
              ct.blocks, bb, ct.blocks / c3, ct.ops / c3, ct.ops / (c3 * log(y) ** 2), ct.evals / max(1, ct.blocks)))
# exact check of the growth inequality 64 H^3 y >= n0^3 on main-phase blocks, and max cf length
def growth_check(y):
    r = isqrt(y); n0 = B.icbrt(y) + 1; bad = 0; nb = 0
    while n0 <= r:
        R = r - n0 + 1; Q = B.icbrt(n0 ** 3 // y)
        a, q = B.approx(y, n0 * n0, Q, B.Ctr())
        if R < q: break
        H = (min(Q, R) // q) * q
        if R >= Q:
            nb += 1
            if not (64 * H ** 3 * y >= n0 ** 3): bad += 1
        n0 += H
    return nb, bad
for e in (6, 9, 12, 15):
    y = 10 ** e + 12345
    print("growth check y=1e%d: main blocks %d, violations %d" % ((e,) + growth_check(y)))
