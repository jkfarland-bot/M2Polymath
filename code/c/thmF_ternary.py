"""Section 7 (F1) check: D_3(x) = 6B - 3E_ab - 3E_bc + m for every 1 <= x <= N.
Truth: d_3 = 1*d by an exact sieve, prefix sums (Python ints).  Formula: vectorised over all x with numpy int64
(all quantities < 2^40, so int64 arithmetic is exact); integer roots by math.isqrt / exact integer cube root.
A pure-Python-int re-evaluation of (F1) is done on a sample of x as an independent cross-check.
Usage: python3 -I thmF_ternary.py [N]"""
import sys
from math import isqrt
import numpy as np

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000

def icbrt(x):
    r = int(round(x ** (1 / 3)))
    while r ** 3 > x:
        r -= 1
    while (r + 1) ** 3 <= x:
        r += 1
    return r

# truth
d2 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d2[j] += 1
d3 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d3[j] += d2[j // i]
D3 = [0] * (N + 1)
for x in range(1, N + 1):
    D3[x] = D3[x - 1] + d3[x]

# formula, vectorised
X = np.arange(N + 1, dtype=np.int64)
m = np.array([0] + [icbrt(x) for x in range(1, N + 1)], dtype=np.int64)
B = np.zeros(N + 1, dtype=np.int64)
Eab = np.zeros(N + 1, dtype=np.int64)
Ebc = np.zeros(N + 1, dtype=np.int64)
for a in range(1, icbrt(N) + 1):
    act = (m >= a)
    y = X // a
    h = np.array([isqrt(int(v)) for v in y], dtype=np.int64)
    Eab += np.where(act, X // (a * a) - a + 1, 0)
    Ebc += np.where(act, h - a + 1, 0)
    for b in range(a, int(h.max()) + 1):
        sel = act & (h >= b)
        B += np.where(sel, y // b - b + 1, 0)
F1 = 6 * B - 3 * Eab - 3 * Ebc + m
bad = [x for x in range(1, N + 1) if int(F1[x]) != D3[x]]
print("N =", N, " (F1) failures:", len(bad), bad[:10])

# pure Python cross-check on a sample
def F1_py(x):
    mm = icbrt(x)
    Bs = Ea = Eb = 0
    for a in range(1, mm + 1):
        ha = isqrt(x // a)
        for b in range(a, ha + 1):
            Bs += x // (a * b) - b + 1
        Ea += x // (a * a) - a + 1
        Eb += ha - a + 1
    return 6 * Bs - 3 * Ea - 3 * Eb + mm
sample = list(range(1, 2001)) + list(range(N - 500, N + 1)) + [k ** 3 + e for k in range(2, icbrt(N)) for e in (-1, 0, 1)]
sbad = [x for x in sample if 1 <= x <= N and F1_py(x) != D3[x]]
print("pure-Python sample size", len(sample), " failures:", len(sbad))
for x in (10 ** 6, 10 ** 7):
    print("spot", x, "F1 =", F1_py(x))
