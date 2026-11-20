import os
# Per-block bounds: CF steps <= log_phi(Q) + 3 and binary-search evaluations <= 9(4 ceil(log2 k) + 1).
import sys, random, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'e'))
import blocksum as B
from math import isqrt
random.seed(11)
phi = (1 + 5 ** 0.5) / 2
worst_cf = 0.0; worst_ev = 0.0; nb = 0
for _ in range(40):
    y = random.randint(10 ** 6, 10 ** random.randint(7, 16))
    r = isqrt(y); n0 = B.icbrt(y) + 1
    while n0 <= r:
        R = r - n0 + 1; Q = B.icbrt(n0 ** 3 // y)
        c1 = B.Ctr(); a, q = B.approx(y, n0 * n0, Q, c1)
        assert c1.cf <= math.log(Q, phi) + 3 + 1e-9
        worst_cf = max(worst_cf, c1.cf - math.log(Q, phi))
        if R < q: break
        k = min(Q, R) // q; H = k * q; s = (q * y) // n0
        ainv = pow(a, -1, q) if q > 1 else 0
        c2 = B.Ctr()
        for j in {0, (q - 2) % q, (q - 1) % q}:
            rho = (ainv * (s - j)) % q; f = (s - a * rho) // q
            for T in (f, f + 1, f + 2):
                B.count_ge(y, T, a, n0 + rho, q, k, c2)
        lim = 9 * (4 * math.ceil(math.log2(k)) + 1) if k > 1 else 9 * 1
        assert c2.evals <= lim, (y, n0, k, c2.evals)
        worst_ev = max(worst_ev, c2.evals / lim)
        nb += 1; n0 += H
print("blocks checked", nb, "max (cf - log_phi Q)", round(worst_cf, 3), "max evals/limit", round(worst_ev, 3))
