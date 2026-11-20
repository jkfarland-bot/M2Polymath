# Seat M2e: provable routine for S(y, L) = sum_{L < b <= isqrt(y)} floor(y/b), any 0 <= L.
# Route B (Vinogradov / Polymath 2012 sec. 2.1 style), with every step made exact:
#   direct columns for b <= icbrt(y); then blocks [n0, n0+H) with
#   Q = floor(n0 / y^(1/3)), a/q a convergent of y/n0^2 with q <= Q, H = q*floor(min(Q,R)/q);
#   linear part summed in closed form, at most 3 "exceptional" residue classes mod q
#   summed exactly by convex level counting (binary search).
# Exact integers only. CHECK=True asserts every intermediate inequality of the proof.
from math import isqrt, gcd
from fractions import Fraction

CHECK = False


def icbrt(n):
    if n < 2:
        return n
    r = int(round(n ** (1.0 / 3)))
    while r * r * r > n:
        r -= 1
    while (r + 1) ** 3 <= n:
        r += 1
    return r


class Ctr:
    def __init__(self):
        self.direct = 0   # floor divisions in direct columns
        self.blocks = 0   # blocks
        self.cf = 0       # continued-fraction steps
        self.evals = 0    # polynomial evaluations in binary searches
        self.maxcf = 0

    @property
    def ops(self):
        return self.direct + self.blocks + self.cf + self.evals


def approx(num, den, Q, ctr):
    """Last convergent p/q of num/den with q <= Q (Lemma 2). Returns (p, q)."""
    p0, q0, p1, q1 = 0, 1, 1, 0      # p_{-2}/q_{-2}, p_{-1}/q_{-1}
    a, b = num, den
    best = None
    steps = 0
    while b:
        t = a // b
        a, b = b, a - t * b
        p0, q0, p1, q1 = p1, q1, t * p1 + p0, t * q1 + q0
        steps += 1
        if q1 > Q:
            break
        best = (p1, q1)
    ctr.cf += steps
    ctr.maxcf = max(ctr.maxcf, steps)
    return best


def count_ge(y, T, a, m, q, k, ctr):
    """#{0 <= l < k : y >= (T - a l)(m + q l)}  (Lemma 4: P concave)."""
    def P(l):
        ctr.evals += 1
        return (T - a * l) * (m + q * l)
    # argmax l* : smallest l in [0, k-1] with P(l+1) - P(l) <= 0, else k-1
    lo, hi = 0, k - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if P(mid + 1) - P(mid) <= 0:
            hi = mid
        else:
            lo = mid + 1
    ls = lo
    if P(ls) <= y:
        return k
    # left: smallest l in [0, ls] with P(l) > y   (P nondecreasing there)
    lo, hi = 0, ls
    while lo < hi:
        mid = (lo + hi) // 2
        if P(mid) > y:
            hi = mid
        else:
            lo = mid + 1
    left = lo
    # right: largest l in [ls, k-1] with P(l) > y (P nonincreasing there)
    lo, hi = ls, k - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if P(mid) > y:
            lo = mid
        else:
            hi = mid - 1
    right = lo
    return k - (right - left + 1)


def S(y, L, ctr):
    r = isqrt(y)
    if L >= r:
        return 0
    c = icbrt(y)
    tot = 0
    n0 = L + 1
    if n0 <= c:
        e = min(c, r)
        tot += sum(y // b for b in range(n0, e + 1))
        ctr.direct += e - n0 + 1
        n0 = e + 1
    while n0 <= r:
        R = r - n0 + 1
        Q = icbrt(n0 ** 3 // y)
        a, q = approx(y, n0 * n0, Q, ctr)
        if CHECK:
            assert Q >= 1 and Q ** 3 * y <= n0 ** 3 < (Q + 1) ** 3 * y
            assert 1 <= q <= Q and gcd(a, q) == 1
            assert abs(y * q - a * n0 * n0) * Q <= n0 * n0          # |alpha - a/q| <= 1/(qQ)
        if R < q:
            tot += sum(y // b for b in range(n0, r + 1))
            ctr.direct += R
            break
        ctr.blocks += 1
        k = min(Q, R) // q
        H = k * q
        s = (q * y) // n0
        if CHECK:
            assert H <= Q and H <= R and 2 * H >= min(Q, R)
        blk = k * s - a * q * k * (k - 1) // 2 - k * (a + 1) * (q - 1) // 2
        if CHECK:
            assert blk == sum((s - a * t) // q for t in range(H))
        ainv = pow(a, -1, q) if q > 1 else 0
        J = {0, (q - 2) % q, (q - 1) % q}
        for j in J:
            rho = (ainv * (s - j)) % q
            m = n0 + rho
            f = (s - a * rho) // q
            cnt = sum(count_ge(y, T, a, m, q, k, ctr) for T in (f, f + 1, f + 2))
            exact = k * (f - 1) + cnt - a * k * (k - 1) // 2
            lin = k * f - a * k * (k - 1) // 2
            if CHECK:
                assert exact == sum(y // (m + q * l) for l in range(k))
            blk += exact - lin
        if CHECK:
            alpha = Fraction(y, n0 * n0)
            for t in range(H):
                n = n0 + t
                g = Fraction(y, n0) - Fraction(a * t, q)
                E = Fraction(y, n) - g
                assert -Fraction(1, q) < E < Fraction(2, q), (y, n0, t)
                E1 = -(alpha - Fraction(a, q)) * t
                E2 = Fraction(y * t * t, n0 * n0 * n)
                assert E == E1 + E2 and abs(E1) < Fraction(1, q) and 0 <= E2 < Fraction(1, q)
                jj = (s - a * t) % q
                if jj not in J:
                    assert y // n == (s - a * t) // q
                rho_t = t % q
                f_t = (s - a * rho_t) // q
                Gfl = y // n + a * (t // q)       # floor(G(l))
                assert f_t - 1 <= Gfl <= f_t + 2
            assert blk == sum(y // (n0 + t) for t in range(H))
        tot += blk
        n0 += H
    return tot


def S_brute(y, L):
    return sum(y // b for b in range(L + 1, isqrt(y) + 1))


def D3_F1(x, ctr):
    """(F1): D_3(x) = 6B - 3E_ab - 3E_bc + m with the inner sums via S."""
    if x <= 0:
        return 0
    m = icbrt(x)
    Bsum = Eab = Ebc = 0
    for a in range(1, m + 1):
        y = x // a
        h = isqrt(y)
        inner = S(y, a - 1, ctr)
        ap = (h * (h - 1) - (a - 1) * (a - 2)) // 2
        Bsum += inner - ap
        Eab += x // (a * a) - a + 1
        Ebc += h - a + 1
    return 6 * Bsum - 3 * Eab - 3 * Ebc + m
