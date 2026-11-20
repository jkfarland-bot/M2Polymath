# Seat M2c-v report: verifier for M2c (A19 D, E, J, K, G), 20 Nov 2026

Saved by the director from the seat's returned text. Scripts: code/cv/{g_verify.py, k_verify.py,
d_verify.py, j_verify.py} (python3 -I, exact integers or Fractions, each under 1 s).

## 1. Theorem G: CONFIRMED
Read in m2/c/dl/lel_v3.pdf (arXiv 1305.1639v3), proof of Theorem 5, page 9: the displayed bound
x^{b/k2 + (1 - b k1/k2) c/k1} needs sum_{d <= U} d^{-b k1/k2} << U^{1 - b k1/k2}, false when b k1 > k2 (sum converges,
term Theta(x^{b/k2})). Counterexample: mu (k1 = 3, a = 2/3), d_3 (k2 = 1, b = 3/5, the paper's (3) with k = 3);
a + b = 19/15 < 2 so the hypothesis holds; c = 18/23, printed 9/23, true first-sum exponent 3/5. Numerically log_x of
the actual work sum is 0.612 to 0.623 for x from 1e12 to 1e23 (printed 0.391).
Example 14 also in the gap regime (dec tau_4 = 2/3, b k1 = 4/3 > 1): true cost 2/3 at the paper's c and over a c-grid;
the proof supports 2/3, not 5/9 (new; agrees with the worker).
Theorem 2 (7/15) stands: Example 13 has b k1 = 2/3, a k2 = 2/3 (valid regime); true cost 7/15, grid minimum; sieve 2/5.
Safe bounds exact: (G2) = 3/5 (b = 3/5) and 5/9 (b = 5/9), printed 9/23 and 17/45; at the paper's c (G2) equals the
true scheme cost in all four cases; in both mod-3 cases the grid minimum over c equals (G2). Printed E1, E2 both equal
(1 - ab)/D at Lelechenko's c; sieve exponents at most that.

## 2. Theorem K: CONFIRMED WITH FIXES
The real K is stated modulo 2^m; the worker's write-up (mod 3^m, M a multiple of 9) is not literally a proof of K, but
the argument is modulus-independent and transfers: L = Q(cuberoot 2, sqrt(-3)), Galois S3, abelian normal subfields only
Q and Q(sqrt(-3)); identity and 3-cycles trivial on Q(sqrt(-3)); Chebotarev gives both kinds of prime q == 1 mod M.
Fix (K text and worker): M must contain 2^m (q^k mod 2^m depends on q mod 2^m); same defect as E.
Witnesses: own form test (q - 27 b^2 a square) agrees with the cubic-residue test for every prime <= 2 * 10^6; 1,559
represented primes <= 1e5 (matches Theorem L). Worker's witnesses correct and least: M = 1260 (6301, 2521); M = 27720
(55441, 388081). New with M = 2^m * 315: m=1 (6301, 631); m=3 (35281, 2521); m=4 (35281, 15121); m=6 (100801, 20161);
m=8 (161281, 241921).

## 3. Theorem D: CONFIRMED pointwise; refutation CONFIRMED WITH QUALIFICATION
d_verify.py builds the mod-9 filter independently (G_A, G_B by convolution; h from (C2) by own series code). n <= 2 * 10^4:
h squarefull-supported; 0 failures (2,328 prime powers give 3; 17,671 integers with omega >= 2 give 0); A(3^e) = 91,
B(3^e) = 0. Worker's thmD.py rerun at N = 10^5 (its default is 2 * 10^4): both filters, 0 pointwise and 0 summed failures.
Against our wording: Q2.3 (mod 2) refuted as a literal list (zeta(s) zeta(s-2) is not a common twist of a listed item;
qualitative clause not contradicted since D2 counts all primes; Q2.3 was posed as "Expected ... complete?", answer no).
Q2.2 (mod 3) refuted literally (shifts 0, 2, 4 are not three equal factors; per-factor twist w = q^2 fails w == 1 mod 3
at q = 3, which F sees: F(3^e) = 273). Spirit survives: for q != 3 the local factor is == (1 - t)^3 mod 3. Restate the
conjecture before calling it dead.

## 4. E fix AGREED; J scope AGREED; 4,143 CONFIRMED
E: q^k mod 9 not determined by q mod 3, so M must include 9 (Theorem C's own M already includes p^m: wording fix).
Rest holds (only h(1) on squarefree n; h(1) a unit; qr and qs differ by 3h(1), nonzero mod 9).
J: scope exactly theta-only linear filters; mixing F components allows non-unit prime values (3, 0) and the
r-periodicity trick does not obviously apply. Formula (2/3)[(c0 + c1) 2^r + (2 c0 - c1)(-1)^r] follows from (T1).
4,143 with no theta counts: splitting from Kronecker (-23/q), principal versus nonprincipal from x^3 - x - 1 mod q;
a_psi from the pentagonal eta series, a_0 from divisor sums of (-23/d). Counts 3,201 / 1,567 / 4,823 / 1 ramified.
Nonprincipal pairs 4,143 (1e5), 929 (2 * 10^4), all (4, 1). (T1) versus eta: 0 mismatches n <= 1e5.

## 5. Script audit
thmD.py not circular (h from the (C2) formula, not target values); default N 2 * 10^4, rerun at 10^5 passes.
thmJ.py: eta check about X^2/2 steps, so its "every n <= 10^5" eta claim probably not produced as written (provenance
unclear; independently confirmed here); prime types defined from computed values (same counts as x^3 - x - 1).
thmG.py part (2) "integer witness" vacuous (hardcoded exponents); real evidence is the analytic step plus the numeric
sum. (G1) partition check genuine. thmK.py framed mod 3^m (item 2).
Not reverified: section 7 (F1) and its cost claim.
