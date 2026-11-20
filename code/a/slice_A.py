"""M2a: numerical check of the Theorem A slice formula over O = Z[i] (cyclotomic, 4th roots of unity).

Random f = sum_i c_i (G_i * h_i): G_i a Dirichlet product of factors ell(chi, s)(n) = chi(n) n^s or their
Dirichlet inverses; characters: trivial, chi_4 (mod 4), an order-4 character mod 5 (values in {1, i, -1, -i}),
principal character mod 3 (imprimitive, level 3), chi_3 (mod 9, imprimitive lift of the character mod 3).
h_i: random Gaussian integers on 1 and on random non-squarefree n, zero elsewhere.
f(n) is computed exactly at chosen n by convolution restricted to divisors of n (no use of multiplicativity).
Slice: squarefree n with all primes = 1 mod M, M = lcm(p^m, all levels).
Check: f(n) = sum_z a_z z^omega(n) mod p^m O, a_z = sum_{z_i = z} c_i h_i(1).
Usage: python3 -I slice_A.py
"""
import random
from math import lcm
from itertools import combinations

random.seed(20261120)


class G:
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = a, b

    def __add__(s, o):
        return G(s.a + o.a, s.b + o.b)

    def __sub__(s, o):
        return G(s.a - o.a, s.b - o.b)

    def __mul__(s, o):
        if isinstance(o, int):
            return G(s.a * o, s.b * o)
        return G(s.a * o.a - s.b * o.b, s.a * o.b + s.b * o.a)

    def mod(s, P):
        return (s.a % P, s.b % P)


ZERO, ONE, I = G(0), G(1), G(0, 1)


def chi_triv(n):
    return ONE


def chi4(n):
    return [ZERO, ONE, ZERO, G(-1)][n % 4]


def chi5(n):  # 2 is a generator mod 5: chi(2) = i
    return {0: ZERO, 1: ONE, 2: I, 4: G(-1), 3: G(0, -1)}[n % 5]


def chi3_principal(n):
    return ZERO if n % 3 == 0 else ONE


def chi9_from3(n):
    return [ZERO, ONE, G(-1)][n % 3]  # level 9 used as the modulus below (imprimitive)


CHARS = [(chi_triv, 1), (chi4, 4), (chi5, 5), (chi3_principal, 3), (chi9_from3, 9)]


def divisors(n):
    ds = [1]
    m = n
    q = 2
    fac = {}
    while q * q <= m:
        while m % q == 0:
            fac[q] = fac.get(q, 0) + 1
            m //= q
        q += 1
    if m > 1:
        fac[m] = fac.get(m, 0) + 1
    for q, e in fac.items():
        ds = [d * q ** j for d in ds for j in range(e + 1)]
    return sorted(ds)


def is_squarefree(n):
    q = 2
    while q * q <= n:
        if n % (q * q) == 0:
            return False
        q += 1
    return True


def factor_fun(chi, s, inverse, divs):
    """values on divs of ell(chi,s) or its Dirichlet inverse (inverse computed recursively on divs)."""
    ell = {d: chi(d) * (d ** s) for d in divs}
    if not inverse:
        return ell
    inv = {}
    for d in divs:
        if d == 1:
            inv[1] = ONE  # ell(1) = 1
            continue
        acc = ZERO
        for e in divs:
            if e < d and d % e == 0:
                acc = acc + inv[e] * ell[d // e]
        inv[d] = ZERO - acc
    return inv


def dconv(f, g, divs):
    out = {}
    for d in divs:
        acc = ZERO
        for e in divs:
            if d % e == 0:
                acc = acc + f[e] * g[d // e]
        out[d] = acc
    return out


def rand_gauss(r=5):
    return G(random.randint(-r, r), random.randint(-r, r))


def make_f(nterms):
    terms = []
    for _ in range(nterms):
        nf = random.randint(0, 4)
        facs = [(random.randrange(len(CHARS)), random.randint(0, 3), random.random() < 0.4) for _ in range(nf)]
        z = sum(-1 if inv else 1 for (_, _, inv) in facs)
        c = rand_gauss()
        hsupp = {1: rand_gauss()}
        for _ in range(4):
            n = random.choice([4, 8, 9, 12, 18, 25, 27, 50, 45, 36, 49, 98, 121])
            hsupp[n] = rand_gauss()
        terms.append((c, facs, z, hsupp))
    return terms


def eval_f(terms, n, divs=None):
    divs = divs if divs is not None else divisors(n)
    total = ZERO
    for c, facs, z, hs in terms:
        g = {d: (ONE if d == 1 else ZERO) for d in divs}
        for ci, s, inv in facs:
            g = dconv(g, factor_fun(CHARS[ci][0], s, inv, divs), divs)
        h = {d: hs.get(d, ZERO) for d in divs}
        total = total + c * dconv(g, h, divs)[n]
    return total


def main():
    p, m = 3, 2
    P = p ** m
    M = lcm(P, *[lv for _, lv in CHARS])
    primes = []
    q = M + 1
    while len(primes) < 6:
        if all(q % t for t in range(2, int(q ** 0.5) + 1)):
            primes.append(q)
        q += M
    print(f"p={p} m={m} M={M} slice primes: {primes}")
    bad = 0
    tot = 0
    for trial in range(40):
        terms = make_f(random.randint(1, 6))
        a = {}
        for c, facs, z, hs in terms:
            a[z] = a.get(z, ZERO) + c * hs[1]
        for r in range(1, 5):
            for combo in combinations(primes, r):
                n = 1
                for q in combo:
                    n *= q
                divs = [1]
                for q in combo:
                    divs = divs + [d * q for d in divs]
                val = eval_f(terms, n, sorted(divs)).mod(P)
                s = ZERO
                for z, az in a.items():
                    s = s + az * (z ** r)  # z negative allowed; integer power
                tot += 1
                if val != s.mod(P):
                    bad += 1
    print(f"slice formula checks: {tot}, failures: {bad}")
    # control: the formula is NOT expected off the slice (non-squarefree or primes not 1 mod M)
    terms = make_f(5)
    a = {}
    for c, facs, z, hs in terms:
        a[z] = a.get(z, ZERO) + c * hs[1]
    offs = 0
    for n in [7 * 11, 12 * 181, 9 * 181, 13 * 17 * 19]:
        r = len([d for d in divisors(n) if d > 1 and all(d % t for t in range(2, d))])
        s = ZERO
        for z, az in a.items():
            s = s + az * (z ** r)
        offs += eval_f(terms, n).mod(P) != s.mod(P)
    print(f"control (off-slice n, formula expected to fail in general): {offs} of 4 differ")


if __name__ == '__main__':
    main()
