import os
# Seat M2d-v: own checks of Result M (x <= 3e4), Theorem L (n, x <= 3e4), Result N (x <= 2e4).
# Methods deliberately differ from m2/d: d_3 and c_L from factorizations (local series),
# h(n) by per-n divisor-pair counting, primes by my own sieve, R by both form search and
# cubic-residue criterion, class number by reduced-form enumeration.
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'dv'))
from math import isqrt, gcd, comb
from hull import icbrt

N = 30000
spf = list(range(N + 1))
for p in range(2, isqrt(N) + 1):
    if spf[p] == p:
        for m in range(p * p, N + 1, p):
            if spf[m] == m:
                spf[m] = p
def fac(n):
    out = []
    while n > 1:
        p = spf[n]; e = 0
        while n % p == 0:
            n //= p; e += 1
        out.append((p, e))
    return out
F = [None, []] + [fac(n) for n in range(2, N + 1)]
isprime = [False, False] + [len(F[n]) == 1 and F[n][0][1] == 1 for n in range(2, N + 1)]
def iroot(x, k):
    if x < 2: return x
    r = int(round(x ** (1.0 / k)))
    while r ** k > x: r -= 1
    while (r + 1) ** k <= x: r += 1
    return r
mu = [0, 1] + [((-1) ** len(F[n]) if all(e == 1 for _, e in F[n]) else 0) for n in range(2, N + 1)]
pi = [0] * (N + 1)
for n in range(1, N + 1): pi[n] = pi[n - 1] + isprime[n]

# ---------- Result M
d3 = [0] + [1] * N
for n in range(2, N + 1):
    v = 1
    for _, e in F[n]: v *= comb(e + 2, 2)
    d3[n] = v
def divisors(n):
    ds = [1]
    for p, e in F[n]:
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return ds
h = [0] * (N + 1)
for n in range(1, N + 1):
    cnt = 0
    for a in divisors(n):
        m = n // a
        for b in divisors(m):
            c = m // b
            if a <= b and a < c: cnt += 1
    h[n] = cnt
bad = {}
D3 = [0] * (N + 1); H = [0] * (N + 1); G = [0] * (N + 1)
for n in range(1, N + 1):
    D3[n] = D3[n - 1] + d3[n]; H[n] = H[n - 1] + h[n]
    g = F[n][0][1] if (n > 1 and len(F[n]) == 1) else 0
    G[n] = G[n - 1] + g
    if d3[n] != (1 if icbrt(n) ** 3 == n else 0) + 3 * h[n]: bad.setdefault('M1pt', n)
    if D3[n] != icbrt(n) + 3 * H[n]: bad.setdefault('M1', n)
for x in range(0, N + 1):
    m = icbrt(x)
    if x >= 1 and sum(mu[d] * (m // d) for d in range(1, m + 1)) != 1: bad.setdefault('cube1', x)
    if x >= 1 and (sum(mu[d] * D3[x // d ** 3] for d in range(1, m + 1)) - 1 - 3 * G[x]) % 9: bad.setdefault('S3', x)
    if (G[x] - sum(mu[d] * H[x // d ** 3] for d in range(1, m + 1))) % 3: bad.setdefault('M2a', x)
    if (H[x] - sum(G[x // d ** 3] for d in range(1, m + 1))) % 3: bad.setdefault('M2b', x)
    if x >= 2:
        L2 = x.bit_length() - 1
        if (pi[x] - G[x] + sum(e * pi[iroot(x, e)] for e in range(2, L2 + 1))) % 3: bad.setdefault('M3', x)
        if pi[x] != sum(mu[j] * j * G[iroot(x, j)] for j in range(1, L2 + 1)): bad.setdefault('M4', x)
# oracle reductions (my own code)
def fwd(x, D3mod9):   # pi(x) mod 3 from a D_3 mod 9 oracle; returns (value, ncalls)
    calls = [0]
    def Hm(y):
        calls[0] += 1
        r = (D3mod9(y) - icbrt(y)) % 9
        assert r % 3 == 0
        return r // 3
    def Gm(y):
        return sum(mu_s(d) * Hm(y // d ** 3) for d in range(1, icbrt(y) + 1))
    if x < 2: return 0, 0
    return sum(mu_s(j) * j * Gm(iroot(x, j)) for j in range(1, x.bit_length()) if j % 3) % 3, calls[0]
def mu_s(n):   # Mobius by trial division (small arguments only)
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0: return 0
            r = -r
        p += 1
    return -r if n > 1 else r
def rev(x, pimod3):   # D_3(x) mod 9 from a pi mod 3 oracle
    def Gm(y):
        return sum(e * pimod3(iroot(y, e)) for e in range(1, y.bit_length())) if y >= 2 else 0
    return (icbrt(x) + 3 * (sum(Gm(x // d ** 3) for d in range(1, icbrt(x) + 1)) % 3)) % 9
fb = sum(1 for x in range(N + 1) if fwd(x, lambda y: D3[y] % 9)[0] != pi[x] % 3)
rb = sum(1 for x in range(N + 1) if rev(x, lambda y: pi[y] % 3) != D3[x] % 9)
print('M: identity failures (first x) x<=%d:' % N, bad or 'none', '; forward oracle failures', fb, '; reverse', rb)
print('   H(3e4)=%d D3(3e4)=%d pi(3e4)=%d' % (H[N], D3[N], pi[N]))

# ---------- Theorem L
# class number of discriminant -108 by reduced primitive forms
forms = []
for a in range(1, 40):
    for b in range(-a + 1, a + 1):
        if (b * b + 108) % (4 * a) == 0:
            c = (b * b + 108) // (4 * a)
            if c >= a and gcd(gcd(a, abs(b)), c) == 1 and not (b < 0 and (a == c)):
                forms.append((a, b, c))
print('L: reduced primitive forms of disc -108:', forms)
rs = [0] * (N + 1)
for a in range(-isqrt(N), isqrt(N) + 1):
    for b in range(-isqrt(N // 27), isqrt(N // 27) + 1):
        n = a * a + 27 * b * b
        if 1 <= n <= N and gcd(a, b) == 1: rs[n] += 1
W = [0] * (N + 1)
for n in range(1, N + 1):
    if gcd(n, 6) == 1:
        W[n] = (2 ** len(F[n])) * rs[n] // 2
inR = [False] * (N + 1)
for q in range(5, N + 1):
    if isprime[q] and rs[q] > 0: inR[q] = True
cubic_dis = sum(1 for q in range(5, N + 1) if isprime[q] and inR[q] != (q % 3 == 1 and pow(2, (q - 1) // 3, q) == 1))
lb = {}
for n in range(1, N + 1):
    f = F[n]
    if n == 1: ok = W[1] == 1
    elif gcd(n, 6) > 1: ok = W[n] == 0
    elif len(f) == 1:
        q, j = f[0]
        ok = W[n] == (4 if (q % 3 == 1 and (inR[q] or j % 3 == 0)) else 0)
    else: ok = W[n] % 8 == 0
    if not ok: lb.setdefault('N2', n)
SW = 0; piR = [0] * (N + 1); pip = [0] * (N + 1)
for i in range(1, N + 1):
    piR[i] = piR[i - 1] + inR[i]; pip[i] = pip[i - 1] + (isprime[i] and i > 3 and i % 3 == 1)
for x in range(1, N + 1):
    SW += W[x]
    CR = sum((pip if j % 3 == 0 else piR)[iroot(x, j)] for j in range(2, x.bit_length()))
    if (SW - 1 - 4 * (piR[x] + CR)) % 8: lb.setdefault('sum8', x)
    if ((SW - 1) // 4 - CR) % 2 != piR[x] % 2 or (SW - 1) % 4: lb.setdefault('N3', x)
print('L: failures', lb or 'none', '; form vs cubic criterion disagreements', cubic_dis, '; |R cap [1,3e4]| =', sum(inR))

# ---------- Result N (x <= 2e4)
NN = 20000
def cL_local(e, L):   # coefficient of t^e in prod_{r<L} (1-t^{3^r})^{-2}
    poly = [1] + [0] * e
    for r in range(L):
        s = 3 ** r
        for _ in range(2):
            for i in range(s, e + 1): poly[i] += poly[i - s]
    return poly[e]
def mloc(e, L):   # (1-t)/(1-t^{3^L}) coefficient
    P = 3 ** L
    return (1 if e % P == 0 else 0) - (1 if e >= 1 and (e - 1) % P == 0 else 0)
cL = {}
nb = 0; first = {}
for L in range(4):
    arr = [0] * (NN + 1)
    for n in range(1, NN + 1):
        v = 1; w = 1
        for p, e in F[n]:
            v *= cL_local(e, L); w *= mloc(e, L)
        arr[n] = v
        if (v - w) % 3: nb += 1
        if L not in first and (v - mu[n]) % 3: first[L] = n
    cL[L] = arr
print('N: (N4) failures n<=2e4, L<=3:', nb, '; first n with c_L != mu mod 3:', first)
def T(j, L, x):
    y = iroot(x, j)
    return sum(cL[L][m] * H[y // m ** 3] for m in range(1, icbrt(y) + 1))
def T_lit(j, L, x):
    ex = [j, j, j] + [j * 3 ** (r + 1) for r in range(L) for _ in (0, 1)]
    def rec(i, prod, vals):
        if i == len(ex):
            return 1 if (vals[0] <= vals[1] and vals[0] < vals[2]) else 0
        t = 0; v = 1
        while prod * v ** ex[i] <= x:
            t += rec(i + 1, prod * v ** ex[i], vals + [v]); v += 1
        return t
    return rec(0, 1, [])
tl = sum(1 for x in list(range(2, 300)) + list(range(300, 1500, 53)) for L in range(3)
         for j in range(1, x.bit_length()) if T(j, L, x) != T_lit(j, L, x))
n5 = 0
for x in range(2, NN + 1):
    L = 0
    while not icbrt(x) < 2 ** (3 ** L): L += 1
    if sum(((j * mu[j]) % 3) * T(j, L, x) for j in range(1, x.bit_length())) % 3 != pi[x] % 3: n5 += 1
print('N: T via c_L vs literal tuples (x<1500 sample, L<=2) failures', tl, '; (N5) least depth failures x<=2e4:', n5)
