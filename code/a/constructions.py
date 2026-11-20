"""M2a: build the claimed Theorem H constructions from (H5)-(H8) and test pointwise on all n <= X.

Everything is computed from definitions:
  d_z = zeta^{*z} for z > 0 (repeated Dirichlet convolution with 1), d_z = mu^{*|z|} for z < 0,
        mu computed as the Dirichlet inverse of 1 by the recursive definition.
  h_z multiplicative with h_z(q^e) = [t^e] (1 + (z-1) t)(1 - t)^(z-1), coefficients by exact
        binomial series (negative exponents included).
  B_z(n) = z^omega(n).
Then d_z * h_z is computed by explicit Dirichlet convolution and compared with B_z for all n <= X.
F_T = sum_z a_z (d_z * h_z) is checked against the target D_k with v = v_p(C), and the
summatory identities (H9), (H10) are checked for every x <= X.
Usage: python3 -I constructions.py [X]
"""
import sys
from fractions import Fraction
from math import comb, factorial, lcm

X = int(sys.argv[1]) if len(sys.argv) > 1 else 100000


def vp(x, p):
    if x == 0:
        return 10 ** 9
    x = abs(x)
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def kempner(m):
    s = 1
    while factorial(s) % m:
        s += 1
    return s


# ---------- arithmetic basics ----------
spf = list(range(X + 1))
for i in range(2, int(X ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, X + 1, i):
            if spf[j] == j:
                spf[j] = i


def factor(n):
    f = {}
    while n > 1:
        q = spf[n]
        f[q] = f.get(q, 0) + 1
        n //= q
    return f


omega = [0] * (X + 1)
for n in range(2, X + 1):
    omega[n] = len(factor(n))
is_prime = [False, False] + [spf[n] == n for n in range(2, X + 1)]
is_ppow = [False] * (X + 1)
for n in range(2, X + 1):
    is_ppow[n] = omega[n] == 1


def conv(f, g):
    h = [0] * (X + 1)
    for d in range(1, X + 1):
        fd = f[d]
        if fd == 0:
            continue
        for m in range(1, X // d + 1):
            gm = g[m]
            if gm:
                h[d * m] += fd * gm
    return h


one = [0] + [1] * X
delta = [0] * (X + 1)
delta[1] = 1
# mu as Dirichlet inverse of 1 from the definition sum_{d|n} mu(d) = delta(n)
mu = [0] * (X + 1)
mu[1] = 1
acc = [0] * (X + 1)  # acc[n] = sum_{d|n, d<n} mu(d)
for d in range(1, X + 1):
    if d > 1:
        mu[d] = -acc[d]
    for m in range(2 * d, X + 1, d):
        acc[m] += mu[d]

_dcache = {0: delta}


def d_fun(z):
    if z in _dcache:
        return _dcache[z]
    step = one if z > 0 else mu
    prev = d_fun(z - 1 if z > 0 else z + 1)
    _dcache[z] = conv(prev, step)
    return _dcache[z]


def series_coeffs(z, E):
    """[t^e] (1 + (z-1) t)(1 - t)^(z-1), e = 0..E, exact."""
    m = z - 1
    # (1 - t)^m = sum_e binom(m, e) (-t)^e with generalized binomial (valid for negative m)
    b = []
    for e in range(E + 1):
        num = 1
        for i in range(e):
            num *= (m - i)
        c = Fraction(num, factorial(e)) * (-1) ** e
        assert c.denominator == 1
        b.append(int(c))
    out = []
    for e in range(E + 1):
        out.append(b[e] + ((z - 1) * b[e - 1] if e >= 1 else 0))
    return out


def h_fun(z):
    E = X.bit_length()
    co = series_coeffs(z, E)
    assert co[0] == 1 and co[1] == 0, (z, co[:3])
    h = [0] * (X + 1)
    h[1] = 1
    for n in range(2, X + 1):
        val = 1
        for q, e in factor(n).items():
            val *= co[e]
            if val == 0:
                break
        h[n] = val
    return h


def check_squarefull(h):
    for n in range(2, X + 1):
        if h[n] and any(e == 1 for e in factor(n).values()):
            return False
    return True


_lift = {}


def lifted(z):
    """d_z * h_z, checked against z^omega(n) for every n <= X."""
    if z in _lift:
        return _lift[z]
    h = h_fun(z)
    assert check_squarefull(h), z
    g = conv(d_fun(z), h)
    for n in range(1, X + 1):
        if g[n] != z ** omega[n]:
            raise AssertionError(f"H7 fails at z={z}, n={n}: {g[n]} vs {z ** omega[n]}")
    _lift[z] = g
    return g


# ---------- (H5) coefficients ----------
def h5_coeffs(nodes):
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


def moments(nodes, a, R):
    return [sum(ai * z ** r for ai, z in zip(a, nodes)) for r in range(1, R + 1)]


# ---------- prefix data for (H9), (H10) ----------
pi_pref = [0] * (X + 1)
for n in range(1, X + 1):
    pi_pref[n] = pi_pref[n - 1] + (1 if is_prime[n] else 0)


def iroot(x, j):
    r = int(round(x ** (1.0 / j)))
    while r ** j > x:
        r -= 1
    while (r + 1) ** j <= x:
        r += 1
    return r


def test_construction(label, nodes, C, a, p, k):
    """Pointwise test of F_T on all n <= X for target D_k with v = v_p(C); return attained k."""
    F = [0] * (X + 1)
    for z, az in zip(nodes, a):
        g = lifted(z)
        for n in range(1, X + 1):
            F[n] += az * g[n]
    v = vp(C, p)
    assert F[1] == sum(a)
    pp_ok = all(F[n] == C for n in range(2, X + 1) if is_ppow[n])
    comp_vals = [F[n] for n in range(2, X + 1) if omega[n] >= 2]
    nz = [vp(x, p) for x in comp_vals if x != 0]
    kmin_attained = (min(nz) - v) if nz else 'all F(n)=0'
    # infinite-domain moment check: s_r = 0 mod p^(v+k) for r = 2 .. max(N,2)+phi(p^N)-1 (all r by periodicity),
    # and the exact value s_(d+1) = -q_0 C
    N = v + k
    P = p ** N
    R = max(N, 2) + p ** N - p ** (N - 1)
    mom_ok = all(sum(az * pow(z, r, P) for z, az in zip(nodes, a)) % P == 0 for r in range(2, R))
    q0 = 1
    for z in nodes:
        q0 *= -z
    d = len(nodes)
    sd1 = sum(az * z ** (d + 1) for z, az in zip(nodes, a))
    mom_ok = mom_ok and sum(az * z for z, az in zip(nodes, a)) == C and sd1 == -q0 * C
    div_C = all(x % C == 0 for x in comp_vals)
    target_ok = pp_ok and all(x % (C * p ** k) == 0 for x in comp_vals)
    # (H9), (H10) for every x <= X
    h9 = h10 = True
    S = 0
    mod9 = C * p ** k
    for x in range(1, X + 1):
        S += F[x]
        J = x.bit_length() - 1  # floor(log2 x)
        ppc = sum(pi_pref[iroot(x, j)] for j in range(1, J + 1))
        if (S - sum(a) - C * ppc) % mod9:
            h9 = False
        num = S - sum(a)
        if num % C:
            h10 = False
        elif (num // C - sum(pi_pref[iroot(x, j)] for j in range(2, J + 1)) - pi_pref[x]) % p ** k:
            h10 = False
    print(f"  {label}: p={p} k={k} C={C} v={v} F(prime powers)=C:{pp_ok} composites div by C:{div_C} "
          f"target D_k:{target_ok} min v_p(F(n)) - v over omega>=2 (n<=X): {kmin_attained} "
          f"[sum v_p(nodes)={sum(vp(z, p) for z in nodes)}] H9:{h9} H10:{h10} all-r moments:{mom_ok}", flush=True)
    return target_ok and h9 and h10 and mom_ok


def main():
    print(f"X = {X}")
    ok_all = True
    # 1. table rows from the extract
    print("Table rows from the extract (positive nodes 1..Z):")
    pos_rows = {2: (2, [4, -1]), 3: (6, [18, -9, 2]), 4: (12, [48, -36, 16, -3]),
                6: (60, [360, -450, 400, -225, 72, -10]),
                9: (2520, [22680, -45360, 70560, -79380, 63504, -35280, 12960, -2835, 280])}
    sgn_rows = {2: (12, [1, -8, 8, -1]), 3: (60, [-1, 9, -45, 45, -9, 1]),
                4: (840, [3, -32, 168, -672, 672, -168, 32, -3]),
                6: (27720, [5, -72, 495, -2200, 7425, -23760, 23760, -7425, 2200, -495, 72, -5])}
    for Z, (C, a) in pos_rows.items():
        nodes = list(range(1, Z + 1))
        Cm, am = h5_coeffs(nodes)
        m = moments(nodes, a, Z + 1)
        print(f"  pos Z={Z}: listed C={C}, H5 minimal C={Cm}, listed==H5:{(C, a) == (Cm, am)}, "
              f"s_1={m[0]}, s_2..s_Z all zero:{all(x == 0 for x in m[1:Z])}")
    for Z, (C, a) in sgn_rows.items():
        nodes = [z for z in range(-Z, Z + 1) if z != 0]
        Cm, am = h5_coeffs(nodes)
        m = moments(nodes, a, 2 * Z + 1)
        print(f"  sgn Z={Z}: listed C={C}, H5 minimal C={Cm}, listed==H5:{(C, a) == (Cm, am)}, "
              f"s_1={m[0]}, s_2..s_2Z all zero:{all(x == 0 for x in m[1:2 * Z])}")
    # 2. pointwise tests: listed rows with the k they should give for p = 2, 3
    print("Pointwise tests of listed rows:")
    for Z, (C, a) in pos_rows.items():
        nodes = list(range(1, Z + 1))
        for p in (2, 3, 5):
            k = vp(factorial(Z), p)
            if k >= 1:
                ok_all &= test_construction(f"pos Z={Z}", nodes, C, a, p, k)
    for Z, (C, a) in sgn_rows.items():
        nodes = [z for z in range(-Z, Z + 1) if z != 0]
        for p in (2, 3, 5):
            k = 2 * vp(factorial(Z), p)
            if k >= 1:
                ok_all &= test_construction(f"sgn Z={Z}", nodes, C, a, p, k)
    # 3. own H5 constructions at the predicted Z for p = 2, 3, 5 and k = 1..4
    print("Own (H5) constructions at the predicted Z, p in {2,3,5}, k = 1..4:")
    for p in (2, 3, 5):
        for k in range(1, 5):
            for signed in (True, False):
                Z = kempner(p ** ((k + 1) // 2)) if signed else kempner(p ** k)
                nodes = [z for z in range(-Z, Z + 1) if z != 0] if signed else list(range(1, Z + 1))
                C, a = h5_coeffs(nodes)
                ok_all &= test_construction(f"{'sgn' if signed else 'pos'} Z={Z}", nodes, C, a, p, k)
    # 4. side claims
    d2, dm2 = d_fun(2), d_fun(-2)
    print(f"Side: d_2(12)={d2[12]}, d_-2(12)={dm2[12]}, d_2-d_-2 at 12 = {d2[12]-dm2[12]} (mod 16: {(d2[12]-dm2[12]) % 16})")
    B2m = [lifted(2)[n] - lifted(-2)[n] for n in range(X + 1)]
    print(f"Side: B_2-B_-2 prime powers all 4: {all(B2m[n] == 4 for n in range(2, X+1) if is_ppow[n])}; "
          f"omega>=2 all = 0 mod 16: {all(B2m[n] % 16 == 0 for n in range(2, X+1) if omega[n] >= 2)}")
    for p in (2, 3, 5):
        Bp = lifted(p)
        vals = [(Bp[n] - delta[n]) for n in range(1, X + 1)]
        okint = all(x % p == 0 for x in vals)
        ok1 = all((Bp[n] - delta[n]) // p == 1 for n in range(2, X + 1) if is_ppow[n])
        ok0 = all(((Bp[n] - delta[n]) // p) % p == 0 for n in range(2, X + 1) if omega[n] >= 2)
        print(f"Side: (B_{p} - delta)/{p}: integer valued {okint}, =1 on prime powers {ok1}, =0 mod {p} for omega>=2 {ok0}, value at 1 = {(Bp[1]-1)//p}")
    print("ALL CONSTRUCTION TESTS PASSED" if ok_all else "SOME CONSTRUCTION TEST FAILED")


if __name__ == '__main__':
    main()
