import os
# Correctness of S_inc against brute force on many (N, L).
import sys, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
from math import isqrt
from hull import S_inc, Ctr, D2_fast

def brute(N, L):
    return sum(N // t for t in range(L + 1, isqrt(N) + 1))

random.seed(20261120)
cnt = bad = 0
# exhaustive: every N <= 3000, every L in [0, isqrt N]
for N in range(1, 3001):
    for L in range(0, isqrt(N) + 1):
        cnt += 1
        if S_inc(N, L, Ctr()) != brute(N, L):
            bad += 1
print('exhaustive N<=3000, all L: cases', cnt, 'failures', bad)
cnt2 = bad2 = 0
# random N up to 1e12 (brute O(sqrt N)), several L each incl. extremes
for e in range(4, 13):
    for _ in range(60 if e <= 10 else 12):
        N = random.randrange(10 ** (e - 1), 10 ** e)
        r = isqrt(N)
        cb = round(N ** (1 / 3))
        Ls = {0, 1, r, r - 1, max(0, cb - 1), cb, cb + 1, random.randrange(0, r + 1), random.randrange(0, cb + 2)}
        for L in Ls:
            if 0 <= L <= r:
                cnt2 += 1
                if S_inc(N, L, Ctr()) != brute(N, L):
                    bad2 += 1
                    print('FAIL', N, L)
print('random N in [1e3,1e12), varied L: cases', cnt2, 'failures', bad2)
# special N: squares, square+-1, cubes, near-squares times
cnt3 = bad3 = 0
for k in list(range(2, 400)) + [10 ** 5, 10 ** 5 + 3, 999999]:
    for N in (k * k - 1, k * k, k * k + 1, k * (k + 1), k * (k + 1) - 1, k ** 3, k ** 3 + 1):
        if N < 1 or N > 10 ** 12:
            continue
        r = isqrt(N)
        for L in {0, r // 2, r - 1, r, round(N ** (1 / 3))}:
            if 0 <= L <= r:
                cnt3 += 1
                if S_inc(N, L, Ctr()) != brute(N, L):
                    bad3 += 1
print('special N (squares, k(k+1), cubes, +-1): cases', cnt3, 'failures', bad3)
# full D2 vs brute at a few N
ok = all(D2_fast(N, Ctr()) == sum(N // t for t in range(1, N + 1)) for N in [1, 2, 3, 10, 99, 1000, 12345, 10 ** 6 + 7])
print('D2_fast vs sum_{t<=N} N//t at 8 values:', ok)
