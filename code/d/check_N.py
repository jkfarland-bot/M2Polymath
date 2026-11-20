import os
# Seat M2d: Result N, c_L coefficients, (N4), tuple counts T_{j,L}, and (N5) at every x <= N.
import sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'd'))
from common import iroot, mobius_sieve, pi_table

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
BR = int(sys.argv[2]) if len(sys.argv) > 2 else 3000   # brute-force tuple range
t0 = time.time()
d2 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d2[j] += 1
mu = mobius_sieve(N)
pi = pi_table(N)

# exact c_L via c_{L+1} = d_2 * E_3(c_L)
c = [[0] * (N + 1)]
c[0][1] = 1
for L in range(4):
    prev, new = c[-1], [0] * (N + 1)
    k = 1
    while k ** 3 <= N:
        if prev[k]:
            k3 = k ** 3
            for t in range(1, N // k3 + 1):
                new[k3 * t] += prev[k] * d2[t]
        k += 1
    c.append(new)

# brute check: c_L(n) = #{n = prod_{r<L} (u_r v_r)^(3^r)}
def count_prod(n, L):
    # number of tuples (u_0,v_0,...,u_{L-1},v_{L-1}) with prod (u_r v_r)^(3^r) = n
    def rec(r, rem):
        if r < 0:
            return 1 if rem == 1 else 0
        e = 3 ** r
        tot = 0
        w = 1
        while w ** e <= rem:
            if rem % (w ** e) == 0:
                # number of (u,v) with uv = w
                nd = sum(1 for u in range(1, w + 1) if w % u == 0)
                tot += nd * rec(r - 1, rem // w ** e)
            w += 1
        return tot
    return rec(L - 1, n) if L > 0 else (1 if n == 1 else 0)
cbad = 0
for L in range(4):
    for n in range(1, 1500):
        if c[L][n] != count_prod(n, L):
            cbad += 1
print('c_L exact vs brute tuple count, L<=3, n<1500: failures', cbad)

# (N4): c_L == mu * E_{3^L}(zeta) mod 3 everywhere; == mu below 2^(3^L); first failure
for L in range(4):
    E = 3 ** L
    first = None; n4bad = 0
    conv = [0] * (N + 1)   # (mu * E_{3^L} 1)(n) = sum_{k^E | n} mu(n/k^E)
    k = 1
    while k ** E <= N:
        kE = k ** E
        for t in range(1, N // kE + 1):
            conv[kE * t] += mu[t]
        k += 1
    for n in range(1, N + 1):
        s = conv[n]
        if (c[L][n] - s) % 3:
            n4bad += 1
        if first is None and (c[L][n] - mu[n]) % 3:
            first = (n, (c[L][n] - mu[n]) % 3)
    print('L=%d: N4 failures %d; first n with c_L != mu mod 3: %s (2^(3^L)=%d); min c_L=%d'
          % (L, n4bad, first, 2 ** (3 ** L), min(c[L][1:])))

# H table via orbit representatives
h = [0] * (N + 1)
a = 1
while a * a * (a + 1) <= N:
    b = a
    while a * b * (a + 1) <= N:
        ab = a * b
        for cc in range(a + 1, N // ab + 1):
            h[ab * cc] += 1
        b += 1
    a += 1
H = [0] * (N + 1)
for i in range(1, N + 1):
    H[i] = H[i - 1] + h[i]

def T(j, L, x):
    y = iroot(x, j)
    return sum(c[L][m] * H[y // m ** 3] for m in range(1, iroot(y, 3) + 1))

# brute literal tuple count for small x
def T_brute(j, L, x):
    exps = [1, 1, 1] + [3 ** (r + 1) for r in range(L) for _ in (0, 1)]
    exps = [e * j for e in exps]
    nv = len(exps)
    cnt = 0
    def rec(i, vals, prod):
        nonlocal cnt
        if i == nv:
            a, b, cc = vals[0], vals[1], vals[2]
            if a <= b and a < cc:
                cnt += 1
            return
        v = 1
        while prod * v ** exps[i] <= x:
            rec(i + 1, vals + [v], prod * v ** exps[i])
            v += 1
    rec(0, [], 1)
    return cnt
tb = 0
for x in list(range(2, 400)) + list(range(400, BR + 1, 37)):
    for L in range(3):
        for j in range(1, x.bit_length()):
            if T(j, L, x) != T_brute(j, L, x):
                tb += 1
print('T_{j,L}(x) via c_L vs literal tuple enumeration (x<=%d sample, L<=2): failures %d' % (BR, tb))

w = [(j * mu[j]) % 3 for j in range(64)]
def least_L(x):
    m = iroot(x, 3); L = 0
    while not m < 2 ** (3 ** L):
        L += 1
    return L
res = {}
for x in range(2, N + 1):
    Ls = least_L(x)
    for L in (0, 1, 2, 3, 'least'):
        LL = Ls if L == 'least' else L
        val = sum(w[j] * T(j, LL, x) for j in range(1, x.bit_length())) % 3
        if val != pi[x] % 3:
            res.setdefault(L, [0, x])[0] += 1
print('N5 failures by depth (count, first x):', res)
print('T_{1,2}(N)=', T(1, 2, N), 'H(N)=', H[N], 'pi(N) mod 3=', pi[N] % 3, 'time %.0f' % (time.time() - t0))
