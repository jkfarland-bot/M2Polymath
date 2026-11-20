import os
# Seat M2d: Result M identities (M1)-(M4), both reductions, at every x <= N and at large x.
import sys, time
from math import isqrt
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'd'))
from common import iroot, mobius_sieve, pi_table, pi_lucy, D3_F1, D3_A25, H_direct

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
t0 = time.time()

# d_3 by Dirichlet convolution d_3 = 1 * d_2 (exact), D_3 prefix
d2 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d2[j] += 1
d3 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d3[j] += d2[j // i]
D3 = [0] * (N + 1)
for i in range(1, N + 1):
    D3[i] = D3[i - 1] + d3[i]

# H by enumerating orbit representatives pointwise: h(n) = #{(a,b,c): abc=n, a<=b, a<c}
h = [0] * (N + 1)
a = 1
while a * a * (a + 1) <= N:
    b = a
    while a * b * (a + 1) <= N:
        ab = a * b
        for c in range(a + 1, N // ab + 1):
            h[ab * c] += 1
        b += 1
    a += 1
H = [0] * (N + 1)
for i in range(1, N + 1):
    H[i] = H[i - 1] + h[i]

cub = [iroot(i, 3) for i in range(N + 1)]
fails = {}
def bad(k, x):
    fails.setdefault(k, x)

# (M1) pointwise and prefix: d_3(n) = [n cube] + 3 h(n)
for n in range(1, N + 1):
    cube = 1 if cub[n] ** 3 == n else 0
    if d3[n] != cube + 3 * h[n]:
        bad('M1_pointwise', n)
    if D3[n] != cub[n] + 3 * H[n]:
        bad('M1_prefix', n)

mu = mobius_sieve(N)
pi = pi_table(N)
LOG2 = [0] * (N + 1)
for x in range(2, N + 1):
    LOG2[x] = x.bit_length() - 1
# G(x) = sum_{q^e<=x} e, exact
G = [0] * (N + 1)
g = [0] * (N + 1)
for q in range(2, N + 1):
    if pi[q] != pi[q - 1]:
        e, qe = 1, q
        while qe <= N:
            g[qe] += e
            e += 1
            qe *= q
for i in range(1, N + 1):
    G[i] = G[i - 1] + g[i]

for x in range(0, N + 1):
    m = cub[x]
    # nested floor root: floor(floor(x/d^3)^(1/3)) == floor(m/d)
    if x <= 20000:
        for d in range(1, m + 1):
            if cub[x // d ** 3] != m // d:
                bad('nested_root', x)
    # cube root terms sum to 1 (x>=1)
    s = sum(mu[d] * (m // d) for d in range(1, m + 1))
    if x >= 1 and s != 1:
        bad('cuberoot_sum', x)
    # S_3(x) = sum mu(d) D3(x/d^3) == 1 + 3G mod 9
    S3 = sum(mu[d] * D3[x // d ** 3] for d in range(1, m + 1))
    if x >= 1 and (S3 - 1 - 3 * G[x]) % 9:
        bad('S3_mod9', x)
    # (M2) first: G == sum mu(d) H(x/d^3) mod 3
    if (G[x] - sum(mu[d] * H[x // d ** 3] for d in range(1, m + 1))) % 3:
        bad('M2_first', x)
    # (M2) second: H == sum G(x/d^3) mod 3
    if (H[x] - sum(G[x // d ** 3] for d in range(1, m + 1))) % 3:
        bad('M2_second', x)
    if x >= 2:
        # (M3)
        rhs = G[x] - sum(e * pi[iroot(x, e)] for e in range(2, LOG2[x] + 1))
        if (pi[x] - rhs) % 3:
            bad('M3', x)
        # (M4) exact
        rhs4 = sum(mu[j] * j * G[iroot(x, j)] for j in range(1, LOG2[x] + 1))
        if rhs4 != pi[x]:
            bad('M4_exact', x)
print('table checks to', N, 'failures:', fails or 'none', 'time %.1f' % (time.time() - t0))
print('H(N)=', H[N], 'D3(N)=', D3[N], 'pi(N)=', pi[N], 'pi mod 3=', pi[N] % 3)

# Reductions as oracle algorithms, with call logging.
class Oracle:
    def __init__(self, f):
        self.f = f; self.calls = []
    def __call__(self, y):
        self.calls.append(y); return self.f(y)

def pi_mod3_from_D3mod9(x, D3mod9, musmall):
    """Forward: D_3 mod 9 oracle -> H mod 3 -> G mod 3 (first M2) -> pi mod 3 (M4)."""
    def Hmod3(y):
        r = (D3mod9(y) - iroot(y, 3)) % 9
        assert r % 3 == 0
        return r // 3
    def Gmod3(y):
        return sum(musmall[d] * Hmod3(y // d ** 3) for d in range(1, iroot(y, 3) + 1)) % 3
    if x < 2:
        return 0
    return sum(musmall[j] * j * Gmod3(iroot(x, j)) for j in range(1, x.bit_length())) % 3

def D3mod9_from_pimod3(x, pimod3):
    """Reverse: pi mod 3 oracle -> G mod 3 -> H mod 3 (second M2) -> D_3 mod 9 via (M1)."""
    def Gmod3(y):
        if y < 2:
            return 0
        return sum(e * pimod3(iroot(y, e)) for e in range(1, y.bit_length())) % 3
    Hm = sum(Gmod3(x // d ** 3) for d in range(1, iroot(x, 3) + 1)) % 3
    return (iroot(x, 3) + 3 * Hm) % 9

fw = rv = 0
musm = mu
for x in range(0, N + 1):
    o = Oracle(lambda y: D3[y] % 9)
    if pi_mod3_from_D3mod9(x, o, musm) != pi[x] % 3:
        fw += 1
    if x <= 20000 or x % 97 == 0:
        o2 = Oracle(lambda y: pi[y] % 3)
        if D3mod9_from_pimod3(x, o2) != D3[x] % 9:
            rv += 1
print('oracle reductions: forward failures', fw, '(all x<=N); reverse failures', rv,
      '(all x<=20000 and every 97th to N)')

# Cost accounting at large x: sum over oracle calls of arg^alpha relative to x^alpha
def calls_forward(x):
    out = []
    for j in range(1, x.bit_length()):
        y = iroot(x, j)
        for d in range(1, iroot(y, 3) + 1):
            out.append(y // d ** 3)
    return out
def calls_reverse(x):
    out = []
    for d in range(1, iroot(x, 3) + 1):
        y = x // d ** 3
        for e in range(1, max(y.bit_length(), 1)):
            out.append(iroot(y, e))
    return out
for X in (10 ** 12, 10 ** 15, 10 ** 18):
    cf, cr = calls_forward(X), calls_reverse(X)
    row = []
    for al in (1 / 3, 0.4, 0.45, 0.49):
        sf = sum(max(y, 1) ** al for y in cf) / X ** max(al, 1 / 3)
        sr = sum(max(y, 1) ** al for y in cr) / X ** max(al, 1 / 3)
        row.append('a=%.3f fw/x^a=%.2f rv/x^a=%.2f' % (al, sf, sr))
    print('X=1e%d calls fw=%d rv=%d (x^(1/3)=%d) ;' % (len(str(X)) - 1, len(cf), len(cr), iroot(X, 3)), '; '.join(row))

# Large-x checks of (M1) and (M2)/(M4) with independent routes
for X in ((10 ** 6, 10 ** 7) if N >= 100000 else (10 ** 5,)):
    t = time.time()
    hd = H_direct(X)
    d3f = D3_F1(X)
    d3a = D3_A25(X)
    print('X=%d H_direct=%d D3_F1=%d D3_A25=%d M1:%s (%.1fs)' % (X, hd, d3f, d3a,
          d3f == d3a == iroot(X, 3) + 3 * hd, time.time() - t))

def H_big(y):
    return (D3_F1(y) - iroot(y, 3)) // 3
def G_big(y):
    return sum(e * pi_lucy(iroot(y, e)) for e in range(1, y.bit_length()))
for X in ((10 ** 8, 10 ** 9 + 7, 3 ** 19) if N >= 100000 else (10 ** 6,)):
    t = time.time()
    m = iroot(X, 3)
    mus = mobius_sieve(m + 1)
    Gx = G_big(X)
    f1 = (Gx - sum(mus[d] * H_big(X // d ** 3) for d in range(1, m + 1))) % 3
    Hx = H_big(X)
    f2 = (Hx - sum(G_big(X // d ** 3) for d in range(1, m + 1))) % 3
    p4 = sum(mus[j] * j * G_big(iroot(X, j)) for j in range(1, X.bit_length()) if j <= m)
    print('X=%d pi=%d M4=%d M2first_ok=%s M2second_ok=%s (%.0fs)' % (X, pi_lucy(X), p4, f1 == 0, f2 == 0, time.time() - t))
