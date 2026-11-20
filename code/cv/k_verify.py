"""Seat M2c-v: Theorem K witnesses (own code). Form test q = a^2 + 27 b^2 by scanning b and testing whether
q - 27 b^2 is a square; cubic-residue test 2^((q-1)/3) = 1 mod q. Rechecks worker witnesses and gives
witnesses with 2^m | M (the stated K is modulo 2^m)."""
from math import isqrt, gcd
X = 2 * 10 ** 6
sv = bytearray([1]) * (X + 1); sv[0] = sv[1] = 0
for i in range(2, isqrt(X) + 1):
    if sv[i]: sv[i*i::i] = bytearray(len(sv[i*i::i]))
def isform(q):
    b = 1
    while 27 * b * b < q:
        r = q - 27 * b * b; a = isqrt(r)
        if a * a == r and a > 0: return True
        b += 1
    return False
mism = 0; nform = 0
for q in range(5, X + 1):
    if sv[q] and q % 3 == 1:
        f = isform(q); c = pow(2, (q - 1) // 3, q) == 1
        nform += f; mism += (f != c)
print("primes q<=", X, "q=1 mod 3: form vs cube-test mismatches:", mism, " represented:", nform)
print("represented primes <= 1e5:", sum(1 for q in range(5, 10**5+1) if sv[q] and q % 3 == 1 and isform(q)))
def first(M):
    r = s = None; q = M + 1
    while q <= X and (r is None or s is None):
        if sv[q]:
            if isform(q):
                r = r or q
            elif s is None: s = q
        q += M
    return r, s
for M, rw, sw in ((1260, 6301, 2521), (27720, 55441, 388081)):
    r, s = first(M)
    print(f"worker M={M}: r={rw} prime {bool(sv[rw])} =1 mod M {rw % M == 1} form {isform(rw)}; "
          f"s={sw} prime {bool(sv[sw])} =1 mod M {sw % M == 1} form {isform(sw)}; my first (r,s)=({r},{s})")
for m in (1, 2, 3, 4, 6, 8, 10):
    M = 2 ** m * 9 * 5 * 7
    print(f"M=2^{m}*315={M}: first r (split), s (3-cycle) = {first(M)}")
