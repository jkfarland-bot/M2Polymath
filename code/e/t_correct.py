import os
# Correctness + every intermediate inequality (CHECK=True) of the M2e proof.
import sys, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'e'))
import blocksum as B
from math import isqrt
B.CHECK = True
random.seed(20261120)
fails = 0; cases = 0
# (1) every y <= 3000, every L in [0, isqrt(y)]
for y in range(1, 3001):
    for L in range(0, isqrt(y) + 1):
        c = B.Ctr(); cases += 1
        if B.S(y, L, c) != B.S_brute(y, L): fails += 1
print("all y<=3000, all L:", cases, "cases, fails", fails)
# (2) random y up to 1e9 with random L, full CHECK (Fraction checks on every n)
f2 = 0; n2 = 0
for _ in range(1500):
    y = random.randint(3001, 10 ** random.randint(4, 9))
    r = isqrt(y)
    for L in (0, random.randint(0, r), B.icbrt(y), r - 1, random.randint(B.icbrt(y), r)):
        n2 += 1
        if B.S(y, L, B.Ctr()) != B.S_brute(y, L): f2 += 1
print("random y<=1e9 (CHECK on):", n2, "fails", f2)
# (3) special forms: squares, k(k+1), cubes, +-1, to ~1e10
f3 = 0; n3 = 0
for k in list(range(2, 400, 7)) + [10**3, 2154, 10**4, 46415, 10**5 - 1]:
    for base in (k * k, k * (k + 1), k ** 3):
        for y in (base - 1, base, base + 1):
            if y < 1 or y > 2 * 10 ** 10: continue
            r = isqrt(y)
            for L in (0, B.icbrt(y), (r + B.icbrt(y)) // 2):
                n3 += 1
                if B.S(y, L, B.Ctr()) != B.S_brute(y, L): f3 += 1
print("special forms (CHECK on):", n3, "fails", f3)
# (4) large y up to 1e13 with CHECK off but block asserts via brute compare
B.CHECK = False
f4 = 0; n4 = 0
for _ in range(60):
    y = random.randint(10 ** 11, 10 ** 13)
    r = isqrt(y)
    for L in (0, random.randint(0, r)):
        n4 += 1
        if B.S(y, L, B.Ctr()) != B.S_brute(y, L): f4 += 1
print("random y in [1e11,1e13]:", n4, "fails", f4)
