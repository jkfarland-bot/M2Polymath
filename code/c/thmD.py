"""Theorem D check: build G_A, G_B as genuine Dirichlet convolutions, build h from (C2) local series,
form A = G_A*h_A, B = G_B*h_B by Dirichlet convolution, then test F mod 9 / mod 4 pointwise and summed.
Exact Python integers.  Usage: python3 -I thmD.py [N]"""
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf

spf = spf_sieve(N)

def factor(n):
    f = {}
    while n > 1:
        p = spf[n]
        f[p] = f.get(p, 0) + 1
        n //= p
    return f

def dconv(f, g):
    h = [0] * (N + 1)
    for d in range(1, N + 1):
        fd = f[d]
        if fd:
            for m in range(1, N // d + 1):
                if g[m]:
                    h[d * m] += fd * g[m]
    return h

def ell(chi_mod, k):
    # completely multiplicative n -> chi(n) n^k, chi principal mod chi_mod (chi_mod=1: trivial)
    return [0] + [(0 if (chi_mod > 1 and n % chi_mod == 0) else n ** k) for n in range(1, N + 1)]

def polymul(a, b, L):
    c = [0] * L
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if i + j < L:
                    c[i + j] += x * y
    return c

def correction(ws, L):
    """local coefficients of h from (C2): (1+(g-1)t)/(1-t) * prod_j (1 - w_j t), eps=+1 for all factors."""
    g = sum(ws)
    s = [1] + [g] * (L - 1)          # (1+(g-1)t)/(1-t) = 1 + g t + g t^2 + ...
    for w in ws:
        s = polymul(s, [1, -w], L)
    return s

def make_h(chi_mod, shifts):
    h = [0] * (N + 1)
    h[1] = 1
    cache = {}
    for n in range(2, N + 1):
        val = 1
        for q, e in factor(n).items():
            if q not in cache:
                L = 1
                while q ** L <= N:
                    L += 1
                ws = [0 if (chi_mod > 1 and q % chi_mod == 0) else q ** k for k in shifts]
                cache[q] = correction(ws, L + 1)
            val *= cache[q][e]
            if val == 0:
                break
        h[n] = val
    return h

def is_squarefull(n):
    return all(e >= 2 for e in factor(n).values())

def omega(n):
    return len(factor(n))

primes = [n for n in range(2, N + 1) if spf[n] == n]

def pi_table():
    t = [0] * (N + 1)
    c = 0
    for n in range(1, N + 1):
        if n >= 2 and spf[n] == n:
            c += 1
        t[n] = c
    return t

PI = pi_table()

def iroot(x, j):
    r = int(round(x ** (1.0 / j)))
    while r ** j > x:
        r -= 1
    while (r + 1) ** j <= x:
        r += 1
    return r

def run(mod, a_coef, b_coef, excl, shifts, unitval):
    GA = ell(1, shifts[0])
    GB = ell(excl, shifts[0])
    for k in shifts[1:]:
        GA = dconv(GA, ell(1, k))
        GB = dconv(GB, ell(excl, k))
    hA = make_h(1, shifts)
    hB = make_h(excl, shifts)
    # h support: squarefull (and h(q)=0 at every prime)
    bad_h = [n for n in range(2, N + 1) if (hA[n] or hB[n]) and not is_squarefull(n)]
    A = dconv(GA, hA)
    B = dconv(GB, hB)
    # exact prime-power values
    bad_pp = 0
    for q in primes:
        e, qe = 1, q
        while qe <= N:
            wantA = sum(q ** k for k in shifts)
            wantB = 0 if q == excl else wantA
            if A[qe] != wantA or B[qe] != wantB:
                bad_pp += 1
            e += 1
            qe *= q
    F = [0] + [a_coef * A[n] - b_coef * B[n] for n in range(1, N + 1)]
    bad_pt = []
    for n in range(1, N + 1):
        w = omega(n)
        want = 1 if n == 1 else (unitval if w == 1 else 0)
        if (F[n] - want) % mod:
            bad_pt.append(n)
    # summed: 1 + unitval * sum_j pi(floor x^(1/j))
    bad_sum = []
    S = 0
    for x in range(1, N + 1):
        S += F[x]
        rhs = 1
        j = 1
        while 2 ** j <= x:
            rhs += unitval * PI[iroot(x, j)]
            j += 1
        if (S - rhs) % mod:
            bad_sum.append(x)
    print(f"mod {mod}: F={a_coef}A-{b_coef}B shifts {shifts}, N={N}")
    print("  h not squarefull-supported:", len(bad_h), bad_h[:5])
    print("  prime-power value mismatches:", bad_pp)
    print("  pointwise failures:", len(bad_pt), bad_pt[:5])
    print("  summed failures:", len(bad_sum), bad_sum[:5])
    print("  sample F(3^e) =", [F[3 ** e] for e in range(1, 4) if 3 ** e <= N], " F(1)=", F[1])

run(9, 3, 2, 3, [0, 2, 4], 3)
run(4, 2, 1, 2, [0, 2], 2)
