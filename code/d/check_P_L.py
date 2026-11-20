import os
# Seat M2d: section 9 (P1),(P2), exponent arithmetic; Theorem L (N1)-(N3).
import sys, time
from math import isqrt, gcd
from fractions import Fraction as F
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'd'))
from common import iroot, mobius_sieve, pi_table, omega_table

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
t0 = time.time()
mu = mobius_sieve(N); pi = pi_table(N); om = omega_table(N)
d2 = [0] * (N + 1)
for i in range(1, N + 1):
    for j in range(i, N + 1, i):
        d2[j] += 1
D = [0] * (N + 1); M = [0] * (N + 1); S2 = [0] * (N + 1)
for i in range(1, N + 1):
    D[i] = D[i - 1] + d2[i]; M[i] = M[i - 1] + mu[i]; S2[i] = S2[i - 1] + 2 ** om[i]

# ---- (P1), (P2)
p1 = p2 = 0
for x in range(1, N + 1):
    U = iroot(x ** 4, 11); V = iroot(x ** 3, 11)
    rhs = (sum(mu[d] * D[x // (d * d)] for d in range(1, U + 1))
           + sum(d2[m] * M[isqrt(x // m)] for m in range(1, V + 1)) - M[U] * D[V])
    if rhs != S2[x]:
        p1 += 1
    if x >= 2:
        par = ((S2[x] - 1) // 2 - sum(pi[iroot(x, j)] for j in range(2, x.bit_length()))) % 2
        if par != pi[x] % 2:
            p2 += 1
print('P1 failures (1<=x<=%d):' % N, p1, '; P2 failures:', p2)
# note: isqrt(x//m) == floor(sqrt(x/m)) exactly
# exponent arithmetic
print('U,V costs:', F(1, 3) + F(1, 3) * F(4, 11), F(1, 4) + F(3, 4) * F(3, 11), ' first correction level:', F(5, 11) / 2)
eps = F(1, 6)
print('Croot exponent 1/4+1/(4+16eps/3) at eps=1/6:', F(1, 4) + 1 / (4 + 16 * eps / 3))
# general balance: x^b U^(1-2b) vs x^(a/2) V^(1-a/2), U^2 V = x
def bal(a, b):
    # b + (1-2b)(1-v)/2 = a/2 + (1-a/2) v
    v = (b + (1 - 2 * b) / 2 - a / 2) / ((1 - a / 2) + (1 - 2 * b) / 2)
    return v, a / 2 + (1 - a / 2) * v
print('balance a=1/2,b=1/3:', bal(F(1, 2), F(1, 3)), ' a=1/2,b=9/28:', bal(F(1, 2), F(9, 28)))
g = 0.6309297535714574  # log_3 2
print('9c: E(log_3 2)=(1+g)/3=%.6f, 5/9=%.6f' % ((1 + g) / 3, 5 / 9))

# ---- Theorem L
rs = [0] * (N + 1)
b = 1
while 27 * b * b <= N:
    a = 0
    while a * a + 27 * b * b <= N:
        if gcd(a, b) == 1:
            n = a * a + 27 * b * b
            rs[n] += 4 if a > 0 else 2   # signs of (a,b); a=0 only possible with b=1 (n=27)
        a += 1
    b += 1
for a in range(1, isqrt(N) + 1):          # b = 0: gcd(a,0)=a, primitive only a=1
    if a == 1:
        rs[1] += 2
W = [0] * (N + 1)
for n in range(1, N + 1):
    if gcd(n, 6) == 1:
        assert (2 ** om[n] * rs[n]) % 2 == 0
        W[n] = 2 ** om[n] * rs[n] // 2
isp = [pi[i] != pi[i - 1] if i else False for i in range(N + 1)]
inR = [False] * (N + 1)
for q in range(5, N + 1):
    if isp[q] and q % 3 == 1 and any(q - 27 * bb * bb >= 0 and isqrt(q - 27 * bb * bb) ** 2 == q - 27 * bb * bb
                                     for bb in range(1, isqrt(q // 27) + 1)):
        inR[q] = True
cubic = sum(1 for q in range(5, N + 1) if isp[q] and ((q % 3 == 1 and pow(2, (q - 1) // 3, q) == 1) != inR[q]))
print('L: form test vs cubic-residue test disagreements:', cubic, '; represented primes <= N:', sum(inR))
pw = 0
ppow = {}
for q in range(5, N + 1):
    if isp[q]:
        j, qj = 1, q
        while qj <= N:
            ppow[qj] = (q, j); j += 1; qj *= q
for n in range(1, N + 1):
    if n == 1:
        ok = W[1] == 1
    elif gcd(n, 6) != 1:
        ok = W[n] == 0
    elif n in ppow:
        q, j = ppow[n]
        exp = 4 if (q % 3 == 1 and (inR[q] or j % 3 == 0)) else 0
        ok = W[n] == exp          # exact (N2)
    else:
        ok = W[n] % 8 == 0 and om[n] >= 2
    if not ok:
        pw += 1
piR = [0] * (N + 1); pip = [0] * (N + 1)
for i in range(1, N + 1):
    piR[i] = piR[i - 1] + inR[i]
    pip[i] = pip[i - 1] + (1 if isp[i] and i > 3 and i % 3 == 1 else 0)
sb = sm = 0; SW = 0
for x in range(1, N + 1):
    SW += W[x]
    CR = sum((pip if j % 3 == 0 else piR)[iroot(x, j)] for j in range(2, x.bit_length()))
    if (SW - 1 - 4 * (piR[x] + CR)) % 8:
        sm += 1
    if (SW - 1) % 4 or ((SW - 1) // 4 - CR - piR[x]) % 2:
        sb += 1
print('L: pointwise (N1)/(N2) failures n<=%d: %d; summed mod 8 failures: %d; parity (N3) failures: %d'
      % (N, pw, sm, sb))
print('time %.0f' % (time.time() - t0))
