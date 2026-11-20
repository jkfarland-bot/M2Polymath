import os
# Estimated total (F1) cost at x = 1e13..1e19 by stratified sampling of shells a.
# Shell cost = steps of S_inc(x//a, a-1) + 3 (exact per sampled shell). Shells a <= A0 exact.
import sys, random, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
from math import isqrt, log
from hull import S_inc, Ctr, icbrt

def shell(x, a):
    c = Ctr(); S_inc(x // a, a - 1, c); return c.steps + 3

random.seed(11)
for e in [int(s) for s in sys.argv[1:]]:
    x = 10 ** e
    m = icbrt(x)
    A0 = 8
    tot = sum(shell(x, a) for a in range(1, A0 + 1))
    K = 40
    edges = sorted(set([A0] + [int(A0 * (m / A0) ** (k / K)) for k in range(1, K)] + [m]))
    var = 0.0
    for lo, hi in zip(edges, edges[1:]):
        n = hi - lo
        if n <= 0:
            continue
        smp = [shell(x, random.randint(lo + 1, hi)) for _ in range(3)]
        mu = sum(smp) / 3
        tot += mu * n
        var += (n * n) * (sum((s - mu) ** 2 for s in smp) / 2) / 3
    print('x=1e%d est steps=%.4g (+-%.2g)  /x^(5/9)=%.3f  /(x^(5/9) ln x)=%.4f  /x^(2/3)=%.5f'
          % (e, tot, var ** 0.5, tot / x ** (5 / 9), tot / (x ** (5 / 9) * log(x)), tot / x ** (2 / 3)))
    sys.stdout.flush()
