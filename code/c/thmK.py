"""Theorem K sanity: primes q = a^2+27b^2 are the q = 1 mod 3 with 2 a cube mod q (split completely in
Q(2^(1/3), zeta_3)).  Check that criterion for q <= X, then for several moduli M (each a multiple of 9 and of
character levels) exhibit primes r, s = 1 mod M with r of the form and s not.  Any f in F has f(q) mod 3^m
depending only on q mod lcm(M, 3^m) at primes q not dividing M, so f(r) = f(s): no pointwise detector.
Usage: python3 -I thmK.py [X]"""
import sys
from math import isqrt

X = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 6
sieve = bytearray([1]) * (X + 1)
sieve[0] = sieve[1] = 0
for i in range(2, isqrt(X) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
form = bytearray(X + 1)
for b in range(1, isqrt(X // 27) + 1):
    for a in range(1, isqrt(X - 27 * b * b) + 1):
        form[a * a + 27 * b * b] = 1
bad = 0
for q in range(5, X + 1):
    if sieve[q] and q % 3 == 1:
        cube = pow(2, (q - 1) // 3, q) == 1
        if cube != bool(form[q]):
            bad += 1
print("X =", X, " criterion mismatches:", bad)
for M in (9, 36, 9 * 4 * 5 * 7, 9 * 8 * 5 * 7 * 11, 27 * 8 * 5 * 7 * 13):
    r = s = None
    q = M + 1
    while q <= X and (r is None or s is None):
        if sieve[q]:
            if form[q] and r is None:
                r = q
            if not form[q] and s is None:
                s = q
        q += M
    print(f"M={M}: r (form) = {r}, s (not form) = {s}")
