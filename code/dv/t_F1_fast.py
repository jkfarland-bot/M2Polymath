import os
# (F1) with the hull-walk incomplete sums: correctness and total cost.
import sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
from math import isqrt, log
from hull import D3_F1_fast, Ctr, icbrt

# independent D_3: (a) pointwise sieve to 3e5; (b) grouped sum_{a<=x} D2(x//a) with plain D2
def d3_prefix(n):
    d = [0] * (n + 1)
    for i in range(1, n + 1):
        for j in range(i, n + 1, i):
            d[j] += 1
    d3 = [0] * (n + 1)
    for i in range(1, n + 1):
        di = d[i]
        for j in range(i, n + 1, i):
            d3[j] += d[j // i]
    out = [0] * (n + 1)
    s = 0
    for i in range(1, n + 1):
        s += d3[i]
        out[i] = s
    return out

def D2_plain(y):
    s = isqrt(y)
    return 2 * sum(y // i for i in range(1, s + 1)) - s * s

def D3_grouped(x):
    tot = 0
    a = 1
    while a <= x:
        q = x // a
        a2 = x // q
        tot += (a2 - a + 1) * D2_plain(q)
        a = a2 + 1
    return tot

P = d3_prefix(300000)
bad = sum(1 for x in range(1, 30001) if D3_F1_fast(x, Ctr()) != P[x])
bad2 = sum(1 for x in range(30001, 300001, 97) if D3_F1_fast(x, Ctr()) != P[x])
print('F1_fast vs sieve: every x<=30000 failures', bad, '; every 97th to 3e5 failures', bad2)
print('D3(1e6) =', D3_F1_fast(10 ** 6, Ctr()), '(record 106030594)')
for x in (10 ** 7, 10 ** 8 + 7, 10 ** 9 + 7, 10 ** 10):
    t = time.time(); v = D3_F1_fast(x, Ctr()); w = D3_grouped(x)
    print('x=%d F1_fast=%d grouped=%d match=%s' % (x, v, w, v == w))
sys.stdout.flush()
print('total steps for (F1) with hull walk:')
for x in (10 ** 9, 10 ** 10, 10 ** 11, 10 ** 12, 10 ** 13):
    c = Ctr(); t0 = time.time(); v = D3_F1_fast(x, c); dt = time.time() - t0
    print('x=1e%d D3=%d steps=%d  /x^(5/9)=%.3f  /(x^(5/9) ln x)=%.4f  /x^(2/3)=%.4f  tail/steps=%.3f  %.0fs'
          % (round(log(x, 10)), v, c.steps, c.steps / x ** (5 / 9), c.steps / (x ** (5 / 9) * log(x)),
             c.steps / x ** (2 / 3), c.tail / c.steps, dt))
    sys.stdout.flush()
