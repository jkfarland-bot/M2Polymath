# Seat M2c report: A19 Theorems D, E, J, K, G and section 7 (worker and cold reader, 20 Nov 2026)

Saved by the director from the seat's returned text (the harness refused the seat's own file write).
Scripts: code/c/{thmD.py, thmJ.py, thmK.py, thmG.py, thmF_ternary.py} (python3 -I, exact arithmetic).
Lelechenko v3 PDF and text: (downloaded source PDFs, not redistributed)
Director note: the seat's extract lacked the Theorem K text (director's extraction error); K below is the seat's own
reconstruction of the brief's statement. The verifier was given the K text.

## Summary
D holds; E holds with a minor fix; J holds (4,143 pairs reproduced exactly); K holds (as reconstructed); G: the gap is
real (exact line and counterexample below); Lelechenko's Theorem 2 (7/15) stands; section 7 (F1) holds for x <= 10^5.

## Theorem D: HOLDS (every n, x <= 10^5)
thmD.py builds G_A, G_B as genuine Dirichlet convolutions of ell(chi, k) and h from the (C2) local series, then
A = G_A * h_A, B = G_B * h_B. Zero failures for F = 3A - 2B (mod 9) and F = 2A - B (mod 4): h_A, h_B squarefull-supported;
A(q^e), B(q^e) equal the stated values at every prime power; F(n) is 1 at n = 1, 3 (resp. 2) at prime powers, 0 when
omega >= 2; (D3) and (D2) hold for every x. Samples F(3^e) = 273, F(2^e) = 10. Proof: for q != 3, q^2 in {1, 4, 7} mod 9
so 1 + q^2 + q^4 == 3 mod 9; for odd q, 1 + q^2 == 2 mod 4; mixed-3 products get 3 * 3.
Caveat: whether this refutes our Q2.2 and Q2.3 depends on their literal wording (not in the seat's inputs).

## Theorem E: HOLDS WITH A MINOR FIX
L cap Q(zeta_M) is abelian, so inside the quadratic resolvent; identity and 3-cycle Frobenius are trivial there, so
Chebotarev gives primes r, s == 1 mod M. On squarefree n: (a_K * h)(n) = h(1) a_K(n); the F part is
sum c_i h_i(1) G_i(n), G_i multiplicative. The prime condition forces 3h(1) == 3u mod 9, so h(1) is a unit; at qr and qs
the core difference is a_K(q) * 3 * h(1) = 3h(1), nonzero mod 9. Contradiction.
Fix: M must also be a multiple of p^m = 9 (power twists chi(q) q^k depend on q mod 9).

## Theorem J: HOLDS (to 10^5)
r_0, r_1 from full lattice-point counts; (T1) confirmed; a_psi equals the eta(z) eta(23z) coefficients for every
n <= 10^5. Prime types (a_0, a_psi): nonprincipal split (2, -1), 3,201 primes; principal split (2, 2), 1,567; inert
(0, 0), 4,823; 23: (1, 1). Nonprincipal pairs q1 < q2, q1 q2 <= 10^5: 4,143, all (4, 1), a_0 - a_psi = 3 (929 at
2 * 10^4). Triples: 1,699, all (8, -1). Multiplicativity: no failures.
Proof: for c0 r0 + c1 r1 the value on r selected primes is (2/3)[(c0 + c1) 2^r + (2 c0 - c1)(-1)^r]; r = 1 and
r = 1 + 2 * 3^m agree mod 3^m (checked m = 1, 2, 3, |c| <= 9); phi(3^(m+1)) even gives the parity of r for free.
Scope: theta-only linear filters, as stated; filters mixing F components are not covered.

## Theorem K: HOLDS (seat's reconstruction)
q = a^2 + 27 b^2 iff q == 1 mod 3 and 2 is a cube mod q (splits completely in Q(2^(1/3), zeta_3)); checked q <= 10^6.
Inside F, f(q) mod p^m depends only on q mod lcm(levels, p^m) (h_i vanish at primes). Identity and 3-cycle Frobenius
are trivial on Q(sqrt(-3)), so for every M there are primes r, s == 1 mod M, r of the form, s not; f(r) = f(s).
Witnesses: M = 1260: r = 6301, s = 2521. M = 27720: r = 55441, s = 388081.

## Theorem G: GAP CONFIRMED
Exact line: Lelechenko v3, proof of Theorem 5, page 9, the displayed step
  y(x) << x^{b/k2 + (1 - b k1/k2) c/k1} + x^{a/k1 + (1 - a k2/k1)(1 - c)/k2} + ...
It silently uses sum_{d <= U} d^{-b k1/k2} << U^{1 - b k1/k2}, valid only for b k1/k2 <= 1 (log at equality). When
b k1 > k2 the sum converges and the term is Theta(x^{b/k2}). The sieve cost x^{c/k1} + x^{(1-c)/k2} is also omitted
(harmless at his c).
Counterexample: mu with k1 = 3, a = 2/3; d_3 with k2 = 1, b = 3/5 (the paper's (3)). c = 18/23, printed bound x^{9/23};
the d = 1 term alone is x^{3/5}; ratio x^{24/115} unbounded. thmG.py checks exactly at x = 2^115 through 2^920.
Safe bound (G2) = max(a/k1, b/k2, T) is valid for the scheme at that c and reduces to the printed formula when
b k1 <= k2 and a k2 <= k1. Mod-3 substitution: 3/5; with b = 5/9: 5/9 (printed 17/45). (G2) is an upper bound at that
c, not the optimum over c in general; no difference here since E1 >= b/k2 for every c.
New, not in A19: the paper's Example 14 (tau_2^2 = mu(d) tau_4(n/d^2), claimed 5/9) is also in the gap regime
(b k1 = 4/3 > 1); the proof supports only 2/3.
(G1) integer-cutoff partition verified for every x <= 2 * 10^4 (mu with d_3, k = 3, 1; mu with d_2, k = 2, 1).
Scope: a gap in the proof, not a disproof of the statement (which, if true here, would give pi(x) mod 3 below sqrt).
Theorem 2 (7/15) depends on Theorem 5 via Example 13 (mu, k1 = 2, a = 2/3; tau_2, k2 = 1, b = 1/3), in the valid
regime (b k1 = 2/3 <= 1, a k2 = 2/3 <= 2); corrected bound still 7/15, sieve cost 2/5. Theorem 2 stands given
dec mu = 2/3 (Deleglise and Rivat) and dec tau_2 = 1/3. Theorem 6 ("strictly below 1") survives.

## Section 7 (F1): HOLDS (every x <= 10^5)
Against an exact D_3 sieve, zero failures; pure-Python cross-check on 2,633 sampled x (including near cubes), zero
failures. Weights 6 (distinct), 3 (a = b < c, a < b = c), 0 + 1 (a = b = c, hence + m). Spot values (not independently
cross-checked): F1(10^6) = 106,030,594; F1(10^7) = 1,421,760,251. Cost claim (x^{5/9} via Sladkey) not tested.

## Least sure
1. K statement reconstructed. 2. Whether D refutes the conjectures as literally worded. 3. Section 7 cost claim.
4. E: M must include p^m. 5. J scope (theta-only linear filters).
