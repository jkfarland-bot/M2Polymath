"""Theorem G / Lelechenko Theorem 5.
(1) exact-rational exponent bookkeeping: printed formula vs the case-split bound, for Example 13 (Theorem 2),
    Example 14, and the modulus-3 substitution (mu, k1=3, a=2/3; d_3, k2=1, b=3/5 or 5/9).
(2) the failing step: sum_{d<=U} (x/d^k1)^(b/k2) is at least its d=1 term x^(b/k2), which exceeds the printed
    x^(b/k2+(1-b k1/k2)c/k1) whenever b k1 > k2.  Integer witness: compare d=1 term with the printed bound via
    exact integer powers at x = 2^(115 t).
(3) the exact partition (G1) with integer cutoffs, checked for f=mu, g=d_3, k1=3, k2=1 and every x <= N, and
    for f=mu, g=d_2, k1=2, k2=1 (Example 13).
Usage: python3 -I thmG.py [N]"""
import sys
from fractions import Fraction as Fr
from math import isqrt

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

def report(name, a, k1, b, k2):
    D = (1 - a) * k2 + (1 - b) * k1
    T = (1 - a * b) / D
    c = (1 - b) * k1 / D
    E1_printed = b / k2 + (1 - b * k1 / k2) * c / k1
    E2_printed = a / k1 + (1 - a * k2 / k1) * (1 - c) / k2
    E1 = b / k2 + max(Fr(0), 1 - b * k1 / k2) * c / k1
    E2 = a / k1 + max(Fr(0), 1 - a * k2 / k1) * (1 - c) / k2
    sieve = max(c / k1, (1 - c) / k2)
    true = max(E1, E2, sieve, a * c / k1, b * (1 - c) / k2)
    G2 = max(a / k1, b / k2, T)
    regime = (b * k1 <= k2) and (a * k2 <= k1)
    print(f"{name}: a={a},k1={k1},b={b},k2={k2}  c={c}  printed dec={T}  E1 printed={E1_printed} true={E1}"
          f"  E2 printed={E2_printed} true={E2}  sieve={sieve}  cost of scheme={true}  (G2)={G2}  valid regime={regime}")

report("Ex13 tau2* (Thm 2)", Fr(2, 3), 2, Fr(1, 3), 1)
report("Ex14 tau2^2", Fr(2, 3), 2, Fr(2, 3), 1)
report("mod3: mu^(3) * d_3, dec d_3 = 3/5", Fr(2, 3), 3, Fr(3, 5), 1)
report("mod3: mu^(3) * d_3, dec d_3 = 5/9", Fr(2, 3), 3, Fr(5, 9), 1)

# (2) integer witness for the mod-3 case: c = 18/23, printed bound exponent 9/23 = 45/115, d=1 term 3/5 = 69/115
for t in (1, 2, 4, 8):
    x = 2 ** (115 * t)
    d1 = 2 ** (69 * t)        # (x/1^3)^(3/5)
    printed = 2 ** (45 * t)   # x^(9/23)
    print(f"x=2^{115*t}: d=1 term / printed bound = 2^{24*t}  (ratio unbounded)", d1 // printed == 2 ** (24 * t))

# (3) (G1) with integer cutoffs U, V where U^k1 * V^k2 <= x < ... any U,V with (U+1)^k1 V^k2 > x etc.
def iroot(x, k):
    r = int(round(x ** (1 / k)))
    while r ** k > x:
        r -= 1
    while (r + 1) ** k <= x:
        r += 1
    return r

mu = [0] * (N + 1); mu[1] = 1
for i in range(1, N + 1):
    for j in range(2 * i, N + 1, i):
        mu[j] -= mu[i]
d2 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d2[j] += 1
d3 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d3[j] += d2[j // i]
def prefix(f):
    P = [0] * (N + 1)
    for i in range(1, N + 1):
        P[i] = P[i - 1] + f[i]
    return P

def check(f, g, k1, k2, cfrac):
    Fp, Gp = prefix(f), prefix(g)
    # h(n) = sum_{u^k1 v^k2 = n} f(u) g(v); H prefix
    h = [0] * (N + 1)
    u = 1
    while u ** k1 <= N:
        v = 1
        while u ** k1 * v ** k2 <= N:
            h[u ** k1 * v ** k2] += f[u] * g[v]
            v += 1
        u += 1
    H = prefix(h)
    bad = 0
    for x in range(1, N + 1):
        U = iroot(int(x ** cfrac) or 1, 1)            # any positive integer cutoff works
        U = max(1, min(U, iroot(x, k1)))
        V = iroot(x // U ** k1, k2)                     # largest V with U^k1 V^k2 <= x
        s1 = sum(f[uu] * Gp[iroot(x // uu ** k1, k2)] for uu in range(1, U + 1))
        s2 = sum(g[vv] * Fp[iroot(x // vv ** k2, k1)] for vv in range(1, V + 1))
        if s1 + s2 - Fp[U] * Gp[V] != H[x]:
            bad += 1
    return bad

print("(G1) mu(u) d_3(v), u^3 v <= x, every x <=", N, "failures:", check(mu, d3, 3, 1, 18 / 23 / 3))
print("(G1) mu(u) d_2(v), u^2 v <= x, every x <=", N, "failures:", check(mu, d2, 2, 1, 0.4))
