"""Theorem J check. r0, r1 = full representation counts of x^2+xy+6y^2 and 2x^2+xy+3y^2 over Z^2.
a_psi = (r0-r1)/2, a_0 = (r0+2r1)/2 (T1).  Checks:
 (1) a_psi equals the q-expansion coefficients of eta(z)eta(23z);
 (2) prime values: nonprincipal split (2,-1), principal split (2,2), inert (0,0);
 (3) every squarefree product q1*q2 <= X of distinct nonprincipal split primes has (a_0,a_psi)=(4,1) (T2),
     also triples (8,-1);
 (4) a_0, a_psi multiplicative on coprime pairs up to X.
Exact integers. Usage: python3 -I thmJ.py [X]"""
import sys
from math import isqrt, gcd

X = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

def reps(a, b, c):
    r = [0] * (X + 1)
    # a x^2 + b xy + c y^2 positive definite; |y| <= sqrt(4 a X / D)
    D = 4 * a * c - b * b
    ymax = isqrt(4 * a * X // D) + 1
    for y in range(-ymax, ymax + 1):
        # solve a x^2 + b y x + c y^2 <= X
        disc = b * b * y * y - 4 * a * (c * y * y - X)
        if disc < 0:
            continue
        s = isqrt(disc)
        lo = (-b * y - s) // (2 * a) - 1
        hi = (-b * y + s) // (2 * a) + 1
        for x in range(lo, hi + 1):
            v = a * x * x + b * x * y + c * y * y
            if 0 < v <= X:
                r[v] += 1
    return r

r0 = reps(1, 1, 6)
r1 = reps(2, 1, 3)
for n in range(1, X + 1):
    assert (r0[n] - r1[n]) % 2 == 0 and (r0[n] + 2 * r1[n]) % 2 == 0
apsi = [0] + [(r0[n] - r1[n]) // 2 for n in range(1, X + 1)]
a0 = [0] + [(r0[n] + 2 * r1[n]) // 2 for n in range(1, X + 1)]

# (1) eta(z) eta(23z) = q * prod (1-q^n)(1-q^{23n})
P = [0] * (X + 1)
P[0] = 1
def mul1m(P, k):  # multiply by (1 - q^k), truncated at degree X-1
    for i in range(X, k - 1, -1):
        P[i] -= P[i - k]
for k in range(1, X):
    mul1m(P, k)
for k in range(23, X, 23):
    mul1m(P, k)
eta_bad = sum(1 for n in range(1, X + 1) if apsi[n] != P[n - 1])
print("X =", X, " eta(z)eta(23z) mismatches:", eta_bad)

sieve = bytearray([1]) * (X + 1)
sieve[0] = sieve[1] = 0
for i in range(2, isqrt(X) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
primes = [i for i in range(2, X + 1) if sieve[i]]
types = {}
for q in primes:
    types.setdefault((a0[q], apsi[q]), []).append(q)
print("prime value types (a0,apsi): count:", {k: len(v) for k, v in types.items()})
nonp = types.get((2, -1), [])
princ = types.get((2, 2), [])

pairs = 0; badpairs = 0
for i, q1 in enumerate(nonp):
    if q1 * q1 >= X:
        break
    for q2 in nonp[i + 1:]:
        n = q1 * q2
        if n > X:
            break
        pairs += 1
        if (a0[n], apsi[n]) != (4, 1) or (a0[n] - apsi[n]) != 3:
            badpairs += 1
print("nonprincipal pairs q1<q2, q1q2<=X:", pairs, " failures of (4,1):", badpairs)

trip = 0; badtrip = 0
for i, q1 in enumerate(nonp):
    if q1 ** 3 > X:
        break
    for j in range(i + 1, len(nonp)):
        q2 = nonp[j]
        if q1 * q2 * q2 > X:
            break
        for q3 in nonp[j + 1:]:
            n = q1 * q2 * q3
            if n > X:
                break
            trip += 1
            if (a0[n], apsi[n]) != (8, -1):
                badtrip += 1
print("nonprincipal triples:", trip, " failures of (8,-1):", badtrip)

# all pairs of split primes (any class) and mixed counts, for comparison with the reported 4,143
split = sorted(nonp + princ)
allpairs = sum(1 for i, a in enumerate(split) for b in split[i + 1:] if a * b <= X)
print("pairs of distinct split primes (any class), product <= X:", allpairs)

# (4) multiplicativity on coprime m,n with mn <= X (sampled exhaustively for m <= 300)
mbad = 0
for m in range(2, 301):
    for n in range(2, X // m + 1):
        if gcd(m, n) == 1:
            if a0[m * n] != a0[m] * a0[n] or apsi[m * n] != apsi[m] * apsi[n]:
                mbad += 1
print("multiplicativity failures (m<=300):", mbad)

# the obstruction itself: for an integral combination c0*r0 + c1*r1, value on r distinct nonprincipal
# primes is (2/3)[(c0+c1)2^r + (2c0-c1)(-1)^r]; verify the r=1 vs r=1+2*3^(m) collision mod 3^m.
for m in (1, 2, 3):
    per = 2 * 3 ** m   # phi(3^(m+1))
    ok = True
    for c0 in range(-9, 10):
        for c1 in range(-9, 10):
            def val(r):
                num = 2 * ((c0 + c1) * 2 ** r + (2 * c0 - c1) * (-1) ** r)
                assert num % 3 == 0
                return num // 3
            if (val(1) - val(1 + per)) % (3 ** m):
                ok = False
    print(f"mod 3^{m}: value at r=1 equals value at r={1+per} for all |c|<=9:", ok)
