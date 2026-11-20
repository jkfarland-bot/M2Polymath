# Seat M2a-v report: verifier for M2a (Theorems A, B, H), 20 Nov 2026

Saved by the director from the seat's returned text. Scripts: code/av/{hnf_levels.py, construct_check.py}
with *_out.txt (python3 -I).

## Verdicts
Theorem H: CONFIRMED WITH FIXES (wording only).
- Lower bound re-derived: z Q(z) = 0 at every node, so q_0 s_1 + ... + q_d s_(d+1) = 0 exactly; s_2..s_(d+1) == 0
  mod p^(v+k) (Theorem A, m = v + k), so q_0 p^v u in p^(v+k) O; u^-1 and torsion-freeness give q_0 in p^k O; O cap Q = Z
  gives p^k | q_0. v cancels. Signed maximum 2 v_p(Z!) correct (each |z| at most twice); 2 v_p(Z!) >= k iff
  Z >= S(p^ceil(k/2)).
- Construction re-derived: Lagrange at 0 gives s_1 = C, s_2..s_d = 0; recurrence gives s_(d+1) = -q_0 C and C q_0
  divides later s_r. (H6) at a prime: (1 - t)^(-z) times it gives 1 + zt/(1 - t), so value z on every prime power;
  integral for negative z; zero linear term, so squarefull-supported. (H9), (H10) correct.
- Fix 1: add the line O cap Q = Z (the extract's "coprime integers are units" clause also silently needs 1/p not in O).
- Fix 2: state D_k explicitly (offset v, modulus p^(v+k), value at 1 free). With modulus p^k independent of v the bound
  becomes k - v <= sum v_p, a different answer.
- Fix 3: keep "v free" in the ledger statement. With v fixed the answers change (v = 0 always impossible by A1).
- Signed degree as the measure is robust: the lower bound holds a fortiori for larger measures (total factor count);
  the construction uses pure powers. Formulas hold for both measures.
Theorem B: CONFIRMED. Euler: z^(1 + t p(p-1)) == z mod p^2 for p not dividing z; r >= 2 kills p | z terms; so
s_1 == p sum_{v_p(z) = 1} a_z (z/p); all such a_z in pO forces u in pO. "Sufficiently large r" can be r >= 2; "nonzero"
redundant. Degree-p claim and mod-9 claim (a_1 == a_2 == 0 mod 9, a_3 unit mod 3, from r = 2, 3) checked by hand.
Theorem A and A1: CONFIRMED. At a slice prime G_i(q) is the sum of factor values (convolution at a prime is additive),
giving z_i; needs h_i supported on 1 and non-squarefree n (implicit in the extract). A1 is Fermat on the integer z.
(B_p - delta)/p example and f^(*p) = E_p(Frob o f) correct.

## Code audit of M2a
No circularity. moments.py: mod-p^N elimination complete (adds kill vector p^(N-e) * pivot); rows 2..d+2 justified by
the exact recurrence; zmax = 60. Real limit: offsets only v <= 8 (closed below). constructions.py checks H7 by direct
convolution; composite test vacuous for >= 6 nodes (omega <= 6 below 10^5), so the moment check carries those rows.
slice_A.py sound (cosmetic label "chi9" for a mod-3 character). brute.py, fixed_v.py fine.

## Independent recomputation (Hermite normal form over Z; every offset covered)
With c = v_p(det Vandermonde), p^N Z_p^d lies in the moment lattice once v >= c and feasibility is upward closed in v,
so "some v works" iff "v = c works"; all v from 0 to c tested.
| p | family | k=1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| 2 | signed | 2 (1) | 2 (2) | 4 (2) | 4 (2) | 4 (3) |
| 2 | cheap | 2 (1) | 4 (2) | 4 (2) | 6 (2) | 8 (3) |
| 3 | signed | 3 (1) | 3 (1) | 6 (2) | 6 (2) | 9 (2) |
| 3 | cheap | 3 (1) | 6 (1) | 9 (2) | 9 (2) | 12 (2) |
| 5 | signed | 5 (1) | 5 (1) | 10 (1) | | |
| 5 | cheap | 5 (1) | 10 (1) | 15 (1) | | |
(least v in parentheses). All 26 entries equal the Kempner formulas and match the extract's and the worker's tables.
Fixed v = 1 (Z <= 16): p = 2 only k = 1; p = 3 k <= 2, none for k = 3, 4.
Constructions (numpy convolution, every n <= 2 * 10^5; d_z from powers of 1 or a sieve Moebius; h_z from explicit
series products, no use of z^omega): p=2 signed Z=2 k=2 (C=12); p=2 signed Z=4 k=6 (C=840); p=3 cheap Z=3 k=1;
p=3 cheap Z=6 k=2; p=5 cheap Z=5 k=1; p=5 signed Z=5 k=2 (C=2520). All pass: F = C on every prime power,
F == 0 mod C p^k for omega >= 2, moments for all r by periodicity; attained level exactly k; negative control
(a_1 + 1) fails in all six.

## Point 5: S(p^k) here versus L(p, k) = S(p^k) - 1 for mu
Exact index shift Z_cheap = L + 1 via a one-way slice reduction: an identity for mu at levels 0..L gives integers c_z
with sum c_z z^r == (-1)^r for r >= 0; convolving with zeta shifts nodes to w = z + 1 in {1..L+1} and the binomial
transform gives moments == [r = 0]; a_w = c_w D / w, D = lcm(1..L+1), gives s_1 = D(1 + p^k m), s_r in D p^k Z for
r >= 2: a cheap D_k slice solution with v = v_p(D), nodes 1..L+1. (H4) gives k <= v_p((L+1)!), so L >= S(p^k) - 1:
a three-line proof of R-053's lower bound from H's. Computation agrees (least mu slice level S(p^k) - 1 for p=2 k<=5,
p=3 k<=3, p=5 k<=2). Converse fails: mu allows only E_p corrections, v = 0, integral c; so R-053's construction is not
implied by H's. Same number, different statements. Recommends a cold read of this reduction before it is recorded.
