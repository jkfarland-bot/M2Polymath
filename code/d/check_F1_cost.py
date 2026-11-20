import os
# Seat M2d: section 7 (F1) spot re-check and cost accounting for the incomplete-sum step.
import sys, time
from math import isqrt
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'd'))
from common import iroot, D3_F1, D3_A25

# (F1) re-check against the independent hyperbola route
bad = 0
for x in list(range(1, 20001)) + list(range(20001, 100001, 101)):
    if D3_F1(x) != D3_A25(x):
        bad += 1
print('F1 vs A25 route, all x<=20000 and every 101st to 1e5: failures', bad)

# Cost proxies for the shells S(y, a, isqrt(y)), y = x//a, a <= x^(1/3).
#  manual(a): Sladkey-style manual columns with lower cutoff a: max(0, ceil((2y)^(1/3)) - a)
#  regions(a): top-level slope bands met on [max(a, xmin), sqrt y]  (~ y / max(a,xmin)^2)
#  leftover(a): columns between the lower cutoff a and the nearest top-level boundary
#               x4 = isqrt(y // k) >= a  (what one gets by stopping the downward sweep and
#               finishing the last band column by column).
for e in (9, 12, 15, 18, 21):
    x = 10 ** e
    m = iroot(x, 3)
    man = reg = left = 0
    for a in range(1, m + 1):
        y = x // a
        s = isqrt(y)
        xmin = min(iroot(2 * y, 3) + 1, s)
        lo = max(a, xmin)
        man += max(0, xmin - a)
        reg += max(0, y // (lo * lo) - 1)
        if a >= xmin:
            k = y // (a * a)           # largest slope index with isqrt(y//k) >= a
            if k >= 1:
                left += isqrt(y // k) - a
    print('x=1e%d: manual/x^(1/2)=%.3f regions/x^(5/9)=%.3f leftover/x^(2/3)=%.4f leftover/x^(5/9)=%.2f'
          % (e, man / x ** 0.5, reg / x ** (5 / 9), left / x ** (2 / 3), left / x ** (5 / 9)))
