import os
# Result M reductions at large x with D_3 from the hull-walk (F1) evaluator and pi from my own
# Lucy-style sieve over the values floor(x/k) (plus tabulated literature values).
import sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
from math import isqrt
from hull import D3_F1_fast, Ctr, icbrt

def iroot(x, k):
    if x < 2: return x
    r = int(round(x ** (1.0 / k)))
    while r ** k > x: r -= 1
    while (r + 1) ** k <= x: r += 1
    return r
def mu_s(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0: return 0
            r = -r
        p += 1
    return -r if n > 1 else r
def prime_count(x):
    if x < 2: return 0
    r = isqrt(x)
    small = [i - 1 for i in range(r + 1)]          # S(i) for i <= r
    large = [0] + [x // k - 1 for k in range(1, r + 1)]   # S(x//k)
    for p in range(2, r + 1):
        if small[p] == small[p - 1]: continue
        sp = small[p - 1]; p2 = p * p
        lim = min(r, x // p2)
        for k in range(1, lim + 1):
            kp = k * p
            large[k] -= (large[kp] if kp <= r else small[x // kp]) - sp
        for i in range(r, p2 - 1, -1):
            small[i] -= small[i // p] - sp
    return large[1]
LIT = {10 ** 10: 455052511, 10 ** 11: 4118054813}
for x in (10 ** 9 + 7, 10 ** 10, 10 ** 11):
    t = time.time(); c = Ctr(); ncall = [0]
    def Hm(y):
        ncall[0] += 1
        r = (D3_F1_fast(y, c) - icbrt(y)) % 9
        assert r % 3 == 0
        return r // 3
    val = sum(mu_s(j) * j * sum(mu_s(d) * Hm(iroot(x, j) // d ** 3) for d in range(1, icbrt(iroot(x, j)) + 1))
              for j in range(1, x.bit_length()) if j % 3) % 3
    ref = LIT.get(x) or prime_count(x)
    print('forward x=%d: pi mod 3 via D3 oracle = %d; reference pi=%d (mod 3 = %d); oracle calls %d; steps %.3g (steps/x^(5/9)=%.1f) %.0fs'
          % (x, val, ref, ref % 3, ncall[0], c.steps, c.steps / x ** (5 / 9), time.time() - t))
    sys.stdout.flush()
print('my prime_count(1e10) =', prime_count(10 ** 10), '(lit 455052511)')
# reverse at x = 1e9+7: pi mod 3 oracle (sieve table to 1e6, prime_count above) -> D_3 mod 9
x = 10 ** 9 + 7
T = 10 ** 6
fl = bytearray([1]) * (T + 1); fl[0] = fl[1] = 0
for p in range(2, isqrt(T) + 1):
    if fl[p]: fl[p * p::p] = bytearray(len(range(p * p, T + 1, p)))
pt = [0] * (T + 1); s = 0
for i in range(T + 1): s += fl[i]; pt[i] = s
pim = lambda y: (pt[y] if y <= T else prime_count(y)) % 3
def Gm(y):
    return sum(e * pim(iroot(y, e)) for e in range(1, y.bit_length())) if y >= 2 else 0
rv = (icbrt(x) + 3 * (sum(Gm(x // d ** 3) for d in range(1, icbrt(x) + 1)) % 3)) % 9
print('reverse x=%d: D3 mod 9 via pi oracle = %d; D3_F1_fast mod 9 = %d' % (x, rv, D3_F1_fast(x, Ctr()) % 9))
