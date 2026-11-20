"""Seat M2c-v: Theorem J spot-checks without theta lattice counts.
Split primes for disc -23: Kronecker (-23/q) = 1. Principal split iff x^3 - x - 1 has a root mod q (Hilbert
class field); nonprincipal split iff no root. a_psi from eta(z)eta(23z) via Euler pentagonal series (sparse),
a_0(n) = sum_{d|n} (-23/d). Count nonprincipal pairs q1<q2, q1 q2 <= X and check (a_0, a_psi) = (4, 1)."""
from math import isqrt
X = 10 ** 5
sv = bytearray([1]) * (X + 1); sv[0] = sv[1] = 0
for i in range(2, isqrt(X) + 1):
    if sv[i]: sv[i*i::i] = bytearray(len(sv[i*i::i]))
P = [q for q in range(2, X + 1) if sv[q]]
def kron(q):  # (-23/q) for prime q
    if q == 23: return 0
    if q == 2: return 1 if (-23) % 8 in (1, 7) else -1
    return 1 if pow(-23 % q, (q - 1) // 2, q) == 1 else -1
def hasroot(q): return any((x * x * x - x - 1) % q == 0 for x in range(q)) if q < 50 else None
def roots_cubic(q):
    # number of roots of x^3-x-1 mod q via gcd(x^q - x, f) degree; use polynomial pow mod f
    def mulmod(a, b):
        c = [0] * 5
        for i in range(3):
            for j in range(3): c[i + j] = (c[i + j] + a[i] * b[j]) % q
        for k in (4, 3):  # x^3 = x + 1
            t = c[k]; c[k] = 0; c[k - 2] = (c[k - 2] + t) % q; c[k - 3] = (c[k - 3] + t) % q
        return c[:3]
    r = [1, 0, 0]; base = [0, 1, 0]; e = q
    while e:
        if e & 1: r = mulmod(r, base)
        base = mulmod(base, base); e >>= 1
    # x^q - x mod f
    g = [(r[0]) % q, (r[1] - 1) % q, r[2] % q]
    return g != [0, 0, 0]  # True means x^q != x mod f, i.e. f does not split completely
types = {"nonp": [], "princ": [], "inert": 0, "ram": 0}
for q in P:
    k = kron(q)
    if k == 0: types["ram"] += 1
    elif k == -1: types["inert"] += 1
    else:
        # for split q, f has 0 or 3 roots; it splits completely iff x^q = x mod f
        (types["nonp"] if roots_cubic(q) else types["princ"]).append(q)
print("nonprincipal split:", len(types["nonp"]), " principal split:", len(types["princ"]), " inert:", types["inert"], " ramified:", types["ram"])
# eta(z)eta(23z) = q * E(q) E(q^23), E = sum (-1)^k q^{k(3k-1)/2}
E = {}
k = 0
while True:
    done = True
    for kk in ((k, -k) if k else (0,)):
        e = kk * (3 * kk - 1) // 2
        if e <= X: E[e] = E.get(e, 0) + (-1) ** abs(kk); done = False
    if done and k: break
    k += 1
apsi = [0] * (X + 1)
for e1, c1 in E.items():
    for e2, c2 in E.items():
        n = 1 + e1 + 23 * e2
        if n <= X: apsi[n] += c1 * c2
chi = [0] * (X + 1)
for d in range(1, X + 1):
    # Kronecker (-23/d) via multiplicativity over prime factors
    pass
spf = [0] * (X + 1)
for i in range(2, X + 1):
    if not spf[i]:
        for j in range(i, X + 1, i):
            if not spf[j]: spf[j] = i
kp = {q: kron(q) for q in P}
chi[1] = 1
for d in range(2, X + 1): chi[d] = chi[d // spf[d]] * kp[spf[d]]
a0 = [0] * (X + 1)
for d in range(1, X + 1):
    if chi[d]:
        for m in range(d, X + 1, d): a0[m] += chi[d]
nonp = types["nonp"]
print("prime values: nonp", {(a0[q], apsi[q]) for q in nonp}, " princ", {(a0[q], apsi[q]) for q in types["princ"]})
pairs = bad = 0; pairs2e4 = 0
for i, q1 in enumerate(nonp):
    if q1 * q1 > X: break
    for q2 in nonp[i + 1:]:
        if q1 * q2 > X: break
        pairs += 1; pairs2e4 += q1 * q2 <= 20000
        bad += (a0[q1 * q2], apsi[q1 * q2]) != (4, 1)
print("nonprincipal pairs <= 1e5:", pairs, " (<= 2e4:", pairs2e4, ")  failures of (4,1):", bad)
# cross-check (T1) at X: a_psi = (r0 - r1)/2 from full lattice counts vs pentagonal eta coefficients
def reps(a, b, c):
    r = [0] * (X + 1); D = 4 * a * c - b * b
    for y in range(-isqrt(4 * a * X // D) - 1, isqrt(4 * a * X // D) + 2):
        for x in range(-isqrt(X) - 30, isqrt(X) + 30):
            v = a * x * x + b * x * y + c * y * y
            if 0 < v <= X: r[v] += 1
    return r
r0, r1 = reps(1, 1, 6), reps(2, 1, 3)
print("(T1) a_psi vs eta mismatches n<=X:", sum(1 for n in range(1, X + 1) if (r0[n] - r1[n]) != 2 * apsi[n]),
      " a_0 vs divisor-sum mismatches:", sum(1 for n in range(1, X + 1) if (r0[n] + 2 * r1[n]) != 2 * a0[n]))
