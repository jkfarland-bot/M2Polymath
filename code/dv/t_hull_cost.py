import os
# Cost of one incomplete sum S_inc(N, L) for N up to 1e18 and varied L; plus brute checks
# at a few larger N (up to ~1e14).
import sys, random, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
from math import isqrt, log
from hull import S_inc, Ctr, icbrt

random.seed(7)
print('brute-force checks at larger N:')
for N in [10 ** 13 + 37, 99999999999973, 10 ** 14]:
    r = isqrt(N)
    for L in [0, icbrt(N) + 5, int(N ** 0.4), r - 3]:
        b = sum(N // t for t in range(L + 1, r + 1))
        print('  N=%d L=%d ok=%s' % (N, L, S_inc(N, L, Ctr()) == b))
print('steps / N^(1/3) (tail columns / N^(1/3)) for L = N^theta:')
for e in range(6, 19, 2):
    N = 10 ** e + random.randrange(10 ** (e - 1))
    row = []
    for th in (0.0, 0.25, 1 / 3, 0.4, 0.45, 0.49):
        L = int(round(N ** th)) if th > 0 else 0
        c = Ctr()
        t0 = time.time()
        S_inc(N, L, c)
        row.append('%.3f(%.3f)' % (c.steps / N ** (1 / 3), c.tail / N ** (1 / 3)))
    print('  N~1e%d: ' % e + '  '.join(row) + '   steps/(N^(1/3) log N) at L=0: %.3f' % (Ctr and 0 or 0))
