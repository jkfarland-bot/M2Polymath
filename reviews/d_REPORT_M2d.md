# Seat M2d report: A19 Results M and N, section 9, Theorem L, section 7 cost (20 Nov 2026)

Saved by the director from the seat's returned text. Scripts in m2/d/ (common.py, check_M.py, check_N.py, check_P_L.py,
check_F1_cost.py; outputs *.out; python3 -I, exact integers). A19's own Lean not looked at.

## 1. Result M: HOLDS, both directions
Every x <= 10^5, zero failures: (M1) pointwise (d_3(n) = [n cube] + 3h(n)) and on prefixes; nested root
floor(floor(x/d^3)^(1/3)) = floor(m/d) (to 20000); sum mu(d) floor(m/d) = 1; S_3(x) == 1 + 3G(x) mod 9; both transforms
in (M2) incl. x = 0; (M3) mod 3; (M4) exact. Reductions run as literal oracle algorithms: D_3 mod 9 to pi mod 3, all
x <= 10^5; pi mod 3 to D_3 mod 9, all x <= 20000 and every 97th to 10^5; zero failures. Large x: at 10^6 and 10^7 direct
H counting, (F1) and the A25 hyperbola formula agree with (M1): D_3(10^6) = 106,030,594, H(10^6) = 35,343,498 (match our
records), D_3(10^7) = 1,421,760,251. (M2), (M4) at 10^8, 10^9 + 7, 3^19 with pi by an independent Lucy method
(pi(10^9 + 7) = 50,847,535). Argument (orbit count, mod 9 lifting via f_3(q^e) = 3e, Mobius inversions, recovery of H)
correct. Wording fix: "two distinct prime factors" should be "at least two".
Cost: forward about x^(1/3) oracle calls; reverse about x^(1/3) log x. Sum of arg^alpha / x^alpha bounded for
alpha = 0.4, 0.45, 0.49 (about 2.7 to 5.7) at x = 10^12, 10^15, 10^18; grows like log x at alpha = 1/3. (M5) right; a fixed
saving below 1/2 survives both ways. Reverse bound for e >= 2 is x^(1/3+o(1)) for alpha < 2/3 (stated max(alpha/2, 1/3)
correct but loose). A sieve to x^(1/3) suffices; uniformity needed: cost <= C_eps y^(alpha+eps) for all y.

## 2. Result N: HOLDS
Exact c_L by recursion matches literal tuple enumeration (L <= 3, n < 1500). (N4) for every n <= 10^5, L = 0..3. First
failure of c_L == mu mod 3 at 2^(3^L) (2, 8, 512 for L = 0, 1, 2; difference 1 mod 3); none for L = 3 to 10^5. T_{j,L}
from the c_L/H convolution matches enumeration (x < 400, every 37th to 2000, L <= 2). (N5): zero failures for every
2 <= x <= 10^5 at least depth and at depths 2, 3. Depth 1 first fails at 1024 (as stated); depth 0 at 16 (not claimed).
H(10^5) = 2,506,268, pi(10^5) mod 3 = 1. Algebra (telescoping from (1-t)^3 == 1 - t^3, c_L(d) for mu(d) when
d <= x^(1/3) < 2^(3^L)) correct. Circuit-size paragraph is a counting-reduction size bound, plausible (L = O(log n)).
Narrative mentions Tulsyan; the identity does not depend on it.

## 3. Section 9: HOLDS (conditional on cited oracles); 9c HOLDS as a conditional calculation
(P1) every x <= 10^5 with exact integer roots for x^(4/11), x^(3/11); (P2) parity every 2 <= x <= 10^5. Exponent
arithmetic exact (x^(1/3) U^(1/3) = x^(1/4) V^(3/4) = x^(5/11); first correction x^(5/22)). Croot's note: exponent
1/4 + 1/(4 + 16 eps/3), eps = 1/6 gives exactly 5/11 (the note is a sketch, assumes D in x^(1/2 - eps), eps < 1/4).
47/104 for a = 1/2, b = 9/28 matches; conditional on Li (unreviewed). Second derivation depends on HKM Theorem 5 (exact
Mertens in y^(1/2+o(1))) and a full D_2 in y^(1/3) (Sladkey; see item 5), not checked here. 9c: N6 algebra correct
(shell sum x^(1-g) a^(4g-3); max(1/2, (1+g)/3); g = log_3 2 gives 0.5436, strictly between 1/2 and 5/9; 4 > 3 and
8 < 9); (1 + 2 beta)/3 < 1/2 iff beta < 1/4; product-2 orbit check correct; the x^(1/2) term from early manual columns is
real (measured 1.41 x^(1/2), 10^9 to 10^21). Per-shell bounds are A19's labelled reading of Sladkey; inherit item 5.

## 4. Theorem L: HOLDS
r*(n) by primitive (a, b) enumeration; 2^omega by sieve. All n <= 10^5, zero failures: W(1) = 1; W = 0 when
gcd(n, 6) > 1; W(q^j) exactly 4 or 0 as (N2); W == 0 mod 8 when omega >= 2. Summed formula mod 8 and parity (N3) every
x <= 10^5. 1559 represented primes to 10^5; form test agrees with "q == 1 mod 3 and 2^((q-1)/3) == 1 mod q". Proof:
disc -108, order Z[3 sqrt(-3)], conductor 6, class number 3 ([1,0,27], [4,+-2,7]), units +-1; q splits iff q == 1 mod 3;
class of the prime over q has order 1 or 3; primitive ideals of norm q^j are p^j and its conjugate; sound. Cost
x^(1+o(1)) right as an upper bound.

## 5. Section 7 cost: (F1) HOLDS; x^(5/9) cost GAP (likely fixable)
(F1) rechecked against the hyperbola route (all x <= 20000, every 101st to 10^5, 10^6, 10^7), zero failures.
Sladkey (arXiv:1206.3369): section 8 states O(n^(5/9)) for T_3 by summing O((n/z)^(1/3)) over z <= n^(1/3); section 9
O(n^(5/9 - c + eps)) with G = 1/log_2 3; A19 quotes both correctly. (F1)'s inner sums are exactly Sladkey's incomplete
sums S(floor(x/a), a, floor(sqrt(x/a))); other terms O(m) boundary sums; (F2) wrapper converges (weight d^(-5/3)).
Gap: Sladkey only asserts S(n, x1, sqrt n) is "a partial result" of computing T(n); his sweep runs down from sqrt(n) with
boundaries only at x4 = floor(sqrt(n/k)); no procedure for an arbitrary lower limit. Stopping at the first boundary
>= a and finishing the band column by column costs Theta(x^(2/3)) in total (measured 0.049 x^(2/3), 10^9 to 10^21;
ratio to x^(5/9) grows 0.49 to 10.55). A19's "Sladkey's interval routine costs O~(y^(1/3))" overstates the source.
Likely fix: region recursion with a vertical cut, or a convex-hull walk from arbitrary x; should add only polylog or
O(y^(1/3)) per shell; supplied by neither A19 nor Sladkey. Sladkey's G argument is semi-formal ("Assume for the
moment"; region size to denominator sum stated, not proved; paper marked draft). A rigorous full D_2 in x^(1/3+o(1))
is assumed throughout sections 7 and 9.

## Least sure
1. Sladkey read via WebFetch digests with short quotes (sweep direction, no arbitrary-x1 procedure, rigour of G).
2. The clipped-band fix cost is judgment, not implemented. 3. HKM Theorem 5 unchecked. 4. Reverse oracle runs sampled
beyond 20000. 5. Lean claims untested.
