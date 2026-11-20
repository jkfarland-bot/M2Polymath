# Shared exact-integer helpers for seat M2d checks.
from math import isqrt, gcd


def iroot(x, k):
    """floor(x^(1/k)) exactly, x >= 0, k >= 1."""
    if x < 2 or k == 1:
        return x
    r = int(round(x ** (1.0 / k)))
    while r ** k > x:
        r -= 1
    while (r + 1) ** k <= x:
        r += 1
    return r


def mobius_sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    isp = bytearray([1]) * (n + 1)
    for p in range(2, n + 1):
        if isp[p]:
            for m in range(2 * p, n + 1, p):
                isp[m] = 0
            for m in range(p, n + 1, p):
                mu[m] = -mu[m]
            pp = p * p
            for m in range(pp, n + 1, pp):
                mu[m] = 0
    return mu


def prime_flags(n):
    isp = bytearray([1]) * (n + 1)
    isp[0] = 0
    if n >= 1:
        isp[1] = 0
    for p in range(2, isqrt(n) + 1):
        if isp[p]:
            isp[p * p::p] = bytearray(len(range(p * p, n + 1, p)))
    return isp


def pi_table(n):
    isp = prime_flags(n)
    t = [0] * (n + 1)
    c = 0
    for i in range(n + 1):
        c += isp[i]
        t[i] = c
    return t


def omega_table(n):
    w = [0] * (n + 1)
    for p in range(2, n + 1):
        if w[p] == 0:
            for m in range(p, n + 1, p):
                w[m] += 1
    return w


def pi_lucy(n):
    """pi(n) by Lucy_Hedgehog, exact, independent of sieves."""
    if n < 2:
        return 0
    r = isqrt(n)
    V = [n // i for i in range(1, r + 1)]
    V += list(range(V[-1] - 1, 0, -1))
    S = {v: v - 1 for v in V}
    for p in range(2, r + 1):
        if S[p] > S[p - 1]:
            sp = S[p - 1]
            p2 = p * p
            for v in V:
                if v < p2:
                    break
                S[v] -= S[v // p] - sp
    return S[n]


def D2(y):
    """sum_{n<=y} d(n), exact, O(sqrt y)."""
    if y <= 0:
        return 0
    s = isqrt(y)
    return 2 * sum(y // i for i in range(1, s + 1)) - s * s


def D3_F1(x):
    """D_3(x) via the A19 (F1) formula with plain inner loops."""
    if x <= 0:
        return 0
    m = iroot(x, 3)
    B = Eab = Ebc = 0
    for a in range(1, m + 1):
        y = x // a
        h = isqrt(y)
        for b in range(a, h + 1):
            B += y // b - b + 1
        Eab += x // (a * a) - a + 1
        Ebc += h - a + 1
    return 6 * B - 3 * Eab - 3 * Ebc + m


def D3_A25(x):
    """D_3(x) via the hyperbola identity D3 = 3A_r - 3B_r + r^3 (independent route)."""
    r = iroot(x, 3)
    A = sum(D2(x // a) for a in range(1, r + 1))
    B = 0
    for a in range(1, r + 1):
        for b in range(1, r + 1):
            B += x // (a * b)
    return 3 * A - 3 * B + r ** 3


def H_direct(x):
    """#{(a,b,c): abc<=x, a<=b, a<c} by direct counting over (a,b)."""
    tot = 0
    a = 1
    while a * a * (a + 1) <= x:
        b = a
        while a * b * (a + 1) <= x:
            tot += x // (a * b) - a
            b += 1
        a += 1
    return tot
