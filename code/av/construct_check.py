"""M2a-v: pointwise test of one (H5)-(H8) construction per prime on every n <= X (default 2*10^5).

Independent of the worker's code: d_z built by repeated numpy Dirichlet convolution with 1 (z > 0) or with
mu (z < 0), mu taken from a linear sieve (Moebius from the factorization, not as an inverse of 1);
h_z multiplicative from (H6) via explicit polynomial products; F_T = sum a_z (d_z * h_z) by convolution.
No use is made of z^omega(n) when building F_T. Then the D_k target with v = v_p(C) is checked at every n,
plus a negative control (perturb one coefficient by 1: must fail).
Usage: python3 -I construct_check.py [X]
"""
import sys
from fractions import Fraction
from math import lcm, factorial
import numpy as np

X = int(sys.argv[1]) if len(sys.argv) > 1 else 200000


def vp(x, p):
    x = abs(int(x))
    if x == 0:
        return 10 ** 9
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


# linear sieve: smallest prime factor, Moebius
spf = np.zeros(X + 1, dtype=np.int64)
primes = []
mu = np.zeros(X + 1, dtype=np.int64)
mu[1] = 1
for i in range(2, X + 1):
    if spf[i] == 0:
        spf[i] = i
        primes.append(i)
        mu[i] = -1
    for q in primes:
        if q > spf[i] or i * q > X:
            break
        spf[i * q] = q
        mu[i * q] = 0 if q == spf[i] else -mu[i]

fact = [None] * (X + 1)


def factor(n):
    f = []
    while n > 1:
        q = int(spf[n]); e = 0
        while n % q == 0:
            n //= q; e += 1
        f.append((q, e))
    return f


facs = [factor(n) if n >= 1 else [] for n in range(X + 1)]
omega = np.array([len(f) for f in facs], dtype=np.int64)
maxe = max((e for f in facs for _, e in f), default=1)


def conv(f, g):
    h = np.zeros(X + 1, dtype=np.int64)
    nzf = np.nonzero(f)[0]
    for d in nzf:
        if d == 0:
            continue
        m = X // d
        h[d:d * m + 1:d] += f[d] * g[1:m + 1]
    return h


one = np.ones(X + 1, dtype=np.int64); one[0] = 0
delta = np.zeros(X + 1, dtype=np.int64); delta[1] = 1
dcache = {0: delta}


def d_fun(z):
    if z not in dcache:
        prev = d_fun(z - 1 if z > 0 else z + 1)
        dcache[z] = conv(prev, one if z > 0 else mu)
    return dcache[z]


def polymul(a, b, E):
    out = [0] * (E + 1)
    for i, x in enumerate(a[:E + 1]):
        for j, y in enumerate(b[:E + 1 - i]):
            out[i + j] += x * y
    return out


def h_coeffs(z, E):
    # (1 - t)^(z-1) by repeated multiplication: (1-t)^m for m >= 0, or (1 + t + t^2 + ...)^(-m) for m < 0
    m = z - 1
    base = [1, -1] if m >= 0 else [1] * (E + 1)
    ser = [1] + [0] * E
    for _ in range(abs(m)):
        ser = polymul(ser, base, E)
    return polymul([1, z - 1], ser, E)


def h_fun(z):
    co = h_coeffs(z, maxe)
    assert co[0] == 1 and co[1] == 0
    h = np.zeros(X + 1, dtype=np.int64); h[1] = 1
    for n in range(2, X + 1):
        v = 1
        for _, e in facs[n]:
            v *= co[e]
            if v == 0:
                break
        h[n] = v
    return h


def h5(nodes):
    a = {}
    for z in nodes:
        L = Fraction(1)
        for t in nodes:
            if t != z:
                L *= Fraction(-t, z - t)
        a[z] = L / z
    C = 1
    for z in nodes:
        C = lcm(C, a[z].denominator)
    return C, [int(a[z] * C) for z in nodes]


def check(F, C, p, k):
    v = vp(C, p)
    ppow = omega == 1
    comp = omega >= 2
    pp_ok = bool(np.all(F[ppow] == C))
    mod = C * p ** k
    comp_ok = bool(np.all(F[comp] % mod == 0))
    return pp_ok, comp_ok, v


def run(label, nodes, p, k):
    C, a = h5(nodes)
    F = np.zeros(X + 1, dtype=np.int64)
    lifts = {}
    for z, az in zip(nodes, a):
        g = conv(d_fun(z), h_fun(z))
        lifts[z] = g
        F += az * g
    pp_ok, comp_ok, v = check(F, C, p, k)
    # exact attained level on n <= X
    vals = F[omega >= 2]
    nzv = [vp(x, p) for x in vals if x != 0]
    att = (min(nzv) - v) if nzv else 'F=0 exactly'
    # all-r moment check mod p^(v+k) (z^r mod p^N periodic from r = N, period | phi(p^N))
    N = v + k; P = p ** N
    mom = all(sum(az * pow(z, r, P) for z, az in zip(nodes, a)) % P == 0 for r in range(2, max(N, 2) + P))
    # negative control: a_1 += 1
    G = F + lifts[nodes[nodes.index(1)]]
    nc = check(G, C, p, k)
    print(f"{label}: p={p} k={k} nodes={nodes[0]}..{nodes[-1]} C={C} v={v} F(1)={F[1]} sum a={sum(a)}"
          f" | F=C on all prime powers <= X: {pp_ok} | F == 0 mod C p^k for omega>=2: {comp_ok}"
          f" | min v_p over omega>=2 minus v: {att} | all-r moments: {mom} | control (a_1+1) passes: {nc[0] and nc[1]}", flush=True)
    return pp_ok and comp_ok and mom and not (nc[0] and nc[1])


def main():
    print(f"X = {X}, max omega = {omega.max()}")
    ok = True
    ok &= run("p=2 signed Z=2", [-2, -1, 1, 2], 2, 2)
    ok &= run("p=3 cheap  Z=3", [1, 2, 3], 3, 1)
    ok &= run("p=5 cheap  Z=5", [1, 2, 3, 4, 5], 5, 1)
    ok &= run("p=2 signed Z=4", [z for z in range(-4, 5) if z], 2, 2 * vp(factorial(4), 2))   # k = 6
    ok &= run("p=3 cheap  Z=6", list(range(1, 7)), 3, vp(factorial(6), 3))                    # k = 2
    ok &= run("p=5 signed Z=5", [z for z in range(-5, 6) if z], 5, 2 * vp(factorial(5), 5))   # k = 2
    print("ALL PASS" if ok else "FAILURE")


if __name__ == '__main__':
    main()
