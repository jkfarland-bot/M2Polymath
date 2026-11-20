"""Seat M2c-v: Theorem D, mod-9 filter F = 3A - 2B, recheck pointwise for every n <= N (own code).
G_A, G_B: Dirichlet convolutions of ell(chi,k), k = 0,2,4. h from (C2): power series of
(1+(g-1)t)/(1-t) * prod_j (1 - w_j t), computed by own truncated series code, assembled multiplicatively.
A = G_A*h_A, B = G_B*h_B by Dirichlet convolution. Nothing is built from the target values."""
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
spf = [0] * (N + 1)
for i in range(2, N + 1):
    if not spf[i]:
        for j in range(i, N + 1, i):
            if not spf[j]: spf[j] = i
def fac(n):
    d = {}
    while n > 1:
        p = spf[n]; d[p] = d.get(p, 0) + 1; n //= p
    return d
def conv(f, g):
    h = [0] * (N + 1)
    for i in range(1, N + 1):
        if f[i]:
            for j in range(1, N // i + 1):
                h[i * j] += f[i] * g[j]
    return h
def ell(excl, k):
    return [0] + [0 if (excl and n % excl == 0) else n ** k for n in range(1, N + 1)]
def series(ws, L):
    g = sum(ws)
    # (1 + (g-1) t) * (1 + t + t^2 + ...)
    s = [1] + [1 + (g - 1)] * (L - 1)
    for w in ws:                       # multiply by (1 - w t)
        s = [s[i] - (w * s[i - 1] if i else 0) for i in range(L)]
    return s
def hfun(excl, ks):
    h = [0] * (N + 1); h[1] = 1; loc = {}
    for n in range(2, N + 1):
        v = 1
        for q, e in fac(n).items():
            if q not in loc:
                loc[q] = series([0 if (excl and q % excl == 0) else q ** k for k in ks], 25)
            v *= loc[q][e]
        h[n] = v
    return h
ks = (0, 2, 4)
GA = conv(conv(ell(0, 0), ell(0, 2)), ell(0, 4))
GB = conv(conv(ell(3, 0), ell(3, 2)), ell(3, 4))
hA, hB = hfun(0, ks), hfun(3, ks)
nsf = sum(1 for n in range(2, N + 1) if (hA[n] or hB[n]) and min(fac(n).values()) < 2)
A, B = conv(GA, hA), conv(GB, hB)
bad = []; cnt = {}
for n in range(1, N + 1):
    w = len(fac(n)); want = 1 if n == 1 else (3 if w == 1 else 0)
    r = (3 * A[n] - 2 * B[n]) % 9
    cnt[(min(w, 2), r)] = cnt.get((min(w, 2), r), 0) + 1
    if r != want: bad.append(n)
print("N =", N, " h not squarefull-supported:", nsf, " pointwise failures mod 9:", len(bad), bad[:5])
print("  (omega class, F mod 9) counts:", dict(sorted(cnt.items())))
print("  A(3^e):", [A[3**e] for e in (1, 2, 3)], " B(3^e):", [B[3**e] for e in (1, 2, 3)], " A(5^2)=", A[25])
