import os
# D_3 via (F1) with the provable routine: vs d_3 sieve, vs the M2dv hull-walk D3, and total cost.
import sys, math, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'e'))
import blocksum as B
sys.path.insert(1, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
import hull as Hh
random.seed(7)
N = 30000
d3 = [0] * (N + 1)
d2 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i): d2[j] += 1
for i in range(1, N + 1):
    for j in range(i, N + 1, i): d3[j] += d2[j // i]
D = 0; fails = 0
for x in range(1, N + 1):
    D += d3[x]
    if B.D3_F1(x, B.Ctr()) != D: fails += 1
print("D3 vs sieve, every x <= 30000: fails", fails)
print("D3(10^6) =", B.D3_F1(10 ** 6, B.Ctr()), "(M2dv: 106030594)")
f = 0
for x in [random.randint(10 ** 5, 10 ** 9) for _ in range(40)] + [10 ** 9 + 7, 10 ** 10]:
    if B.D3_F1(x, B.Ctr()) != Hh.D3_F1_fast(x, Hh.Ctr()): f += 1
print("D3 vs M2dv hull D3 at 42 values up to 1e10: fails", f)
for e, dvsteps in ((9, 1.60e6), (11, 2.30e7), (13, 3.219e8)):
    x = 10 ** e
    ct = B.Ctr(); B.D3_F1(x, ct)
    tot = ct.ops + 3 * B.icbrt(x)
    x59 = x ** (5 / 9.0)
    bound = 1.5 * x59  # sum_{a<=m} a^(-1/3) <= 1.5 m^(2/3) (times per-call factor)
    print("x=1e%d ops %.3e  ops/x^(5/9) %.1f  ops/(x^(5/9) ln^2 x) %.4f  M2dv walk steps %.3e (ratio %.2f)" %
          (e, tot, tot / x59, tot / (x59 * math.log(x) ** 2), dvsteps, tot / dvsteps))
# check sum_{a<=m} (x/a)^(1/3) <= 1.5 x^(5/9)
for e in (6, 9, 12, 15):
    x = 10 ** e; m = B.icbrt(x)
    s = sum((x / a) ** (1 / 3.0) for a in range(1, m + 1))
    print("x=1e%d: sum (x/a)^(1/3) / x^(5/9) = %.4f (<= 1.5)" % (e, s / x ** (5 / 9.0)))
