"""Seat M2c-v: Theorem G / Lelechenko v3 Theorem 5, exact rational exponent bookkeeping (own code).
For each case: printed dec (1-ab)/((1-a)k2+(1-b)k1), Lelechenko's c, the true exponent of each work sum
(case split on b k1/k2 and a k2/k1), sieve cost, (G2), and the minimum over c in a rational grid of the
true scheme cost. Also a numeric illustration of the failing sum for the mod-3 substitution."""
from fractions import Fraction as Q
import math

def sumexp(base, s, cut):
    # exponent of x in x^base * sum_{d <= x^cut} d^(-s): base + max(0, 1-s)*cut (log factor at s = 1)
    return base + max(Q(0), 1 - s) * cut

def scheme(a, k1, b, k2, c):
    U, V = c / k1, (1 - c) / k2          # log_x of cutoffs
    W1 = sumexp(b / k2, b * k1 / k2, U)  # sum_{d<=U} (x/d^k1)^(b/k2)
    W2 = sumexp(a / k1, a * k2 / k1, V)  # sum_{d<=V} (x/d^k2)^(a/k1)
    last = max(a * U, b * V)
    sieve = max(U, V)
    return max(W1, W2, last, sieve), W1, W2

def case(name, a, k1, b, k2):
    D = (1 - a) * k2 + (1 - b) * k1
    T = (1 - a * b) / D
    c = (1 - b) * k1 / D
    W1p = b / k2 + (1 - b * k1 / k2) * c / k1      # printed (no case split)
    W2p = a / k1 + (1 - a * k2 / k1) * (1 - c) / k2
    cost, W1, W2 = scheme(a, k1, b, k2, c)
    G2 = max(a / k1, b / k2, T)
    grid = [Q(i, 2000) for i in range(1, 2000)]
    best = min((scheme(a, k1, b, k2, cc)[0], cc) for cc in grid + [c])
    print(f"{name}: a={a} k1={k1} b={b} k2={k2} | a+b<2: {a+b<2} | bk1/k2={b*k1/k2} ak2/k1={a*k2/k1}")
    print(f"   printed dec={T}, c={c}; printed W1={W1p}, W2={W2p}; true W1={W1}, W2={W2}")
    print(f"   true scheme cost at c = {cost}; (G2) = {G2}; equal: {cost == G2}; min over c-grid = {best[0]} at c={best[1]}")

case("Ex13 tau2* (Thm 2)", Q(2, 3), 2, Q(1, 3), 1)
case("Ex14 tau2^2 = mu^(2)*tau4", Q(2, 3), 2, 1 - Q(4, 3 * 4), 1)     # dec tau4 by (3): 1-4/(3*4)
case("mod3 mu^(3)*d3, dec d3=3/5 by (3)", Q(2, 3), 3, 1 - Q(4, 3 * 3 + 1), 1)
case("mod3 mu^(3)*d3, dec d3=5/9", Q(2, 3), 3, Q(5, 9), 1)

# numeric illustration, mod-3 case: work sum S = sum_{d<=U} (x/d^3)^(3/5), U = x^(6/23)
for e in (12, 16, 20, 23):
    x = 10.0 ** e
    U = int(x ** (6 / 23))
    S = sum((x / d ** 3) ** 0.6 for d in range(1, U + 1))
    print(f"x=1e{e}: U={U}, log_x(work sum)={math.log(S)/math.log(x):.4f}, printed exponent 9/23={9/23:.4f}, 3/5=0.6")
