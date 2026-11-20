# Seat M2a report: Theorems A, B, H of A19 (worker and cold reader, 20 Nov 2026)

Saved by the director from the seat's returned text (the harness refused the seat's own file write).
Scripts: code/a/{moments.py, brute.py, constructions.py, slice_A.py, fixed_v.py} with *_out.txt.

## Verdicts
- Theorem H: holds (proved line by line, both directions).
  - Lower bound: k <= sum over the nonzero-degree set T of v_p(z), uniform in v (v cancels). One unstated step:
    p^k O meets Z in p^k Z (O cap Q = Z); add a line. Read "whenever (H4) holds" as "whenever v_p(q_0) >= k".
  - Construction: in F, integral, h_z supported on 1 and squarefull n, equals z^omega(n) on every positive n; attains
    S(p^ceil(k/2)) signed and S(p^k) cheap.
  - The result needs v free. With v fixed the answers change (v = 1, p = 2: nothing for k >= 2 up to Z = 40;
    v = 1, p = 3: nothing for k >= 3 up to Z = 40). Computed only.
- Theorem B: holds. "Sufficiently large r" can be r >= 2. Exact form: sum of a_z (z/p) over v_p(z) = 1 is == u mod pO.
- Theorem A and Corollary A1: hold; they match our O1.

## 0. Definitions as read
D_k with offset v: f(q) = p^v u_q mod p^(v+k) O at every prime q, u_q a unit; f(n) = 0 mod p^(v+k) for omega(n) >= 2;
value at 1 free; the lower bound also leaves q^e (e >= 2) free. Theorem B's D is D_1 with v = 1. The lower bound uses
only primes and squarefree n on the slice; the construction meets the strongest form (exactly C on every prime power),
so the equalities hold for every target between the two.

## 1. Theorem H
(a) Lower bound. Uses Theorem A with m = v + k and d + 1 slice primes. Needs O torsion-free with O cap Q = Z; on h_i only
h_i = 0 on squarefree n > 1. z Q(z) = 0 for every node gives sum q_j s_(j+1) = 0 exactly in O; s_2..s_(d+1) vanish, so
q_0 p^v u == 0 mod p^(v+k); torsion-freeness gives q_0 in p^k O, and O cap Q = Z gives p^k | q_0. v plays no role.
T empty gives q_0 = 1, a contradiction. Maximum of sum v_p over nodes: 2 v_p(Z!) signed, v_p(Z!) cheap, whence
S(p^ceil(k/2)) and S(p^k).
(b) Construction. Lagrange interpolation gives s_1 = C and s_r = 0 for 2 <= r <= d; the exact recurrence gives
s_(d+1) = -q_0 C, and C q_0 divides every s_r, r >= 2. (H6) is integral for every integer z, has linear coefficient 0
(so h_z is squarefull-supported), and d_z * h_z = z^omega(n). d_z is z zeta factors (z > 0) or |z| inverse factors
(z < 0): in F, and in the cheap part when nodes are positive. F_T is C on every prime power and 0 mod C p^k when
omega(n) >= 2, on all n. (H9), (H10) correct; v = v_p(C) depends on the chosen C. The set of working v is upward closed.

## 2. Theorem B
p not dividing z: Euler gives z^r == z mod p^2; p | z: z^r == 0 mod p^2 for r >= 2. So s_1 == sum over v_p(z) = 1 of
a_z z = p sum a_z (z/p); torsion-freeness gives the contradiction if all such a_z lie in pO. The degree-p claim and the
degrees 1, 2, 3 mod 9 claim are exact: only a_1 == a_2 == 0 mod 9 with a_3 a unit mod 3.

## 3. Theorem A, A1
At a prime each plain factor contributes 1 and each inverse factor -1 mod p^m; multiplicativity gives z^r; h_i enters
only through h_i(1). A1 is Fermat on the integer z (no Frobenius on a_z). The (B_p - delta)/p example and
f^(*p) = E_p(Frob o f) are correct.

## 4. Tables (least Z over v <= 8; every entry equals the Kempner formula; extract's table matches)
| p | family | k=1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| 2 | signed | 2 | 2 | 4 | 4 | 4 | 4 | 6 | 6 |
| 2 | cheap | 2 | 4 | 4 | 6 | 8 | 8 | 8 | 10 |
| 3 | signed | 3 | 3 | 6 | 6 | 9 | 9 | | |
| 3 | cheap | 3 | 6 | 9 | 9 | 12 | 15 | | |
| 5 | signed | 5 | 5 | 10 | 10 | 15 | | | |
| 5 | cheap | 5 | 10 | 15 | 20 | 25 | | | |
| 7 | signed | 7 | 7 | 14 | 14 | | | | |
| 7 | cheap | 7 | 14 | 21 | 28 | | | | |

Least v at that Z (signed and cheap alike): p=2: 1,2,2,2,3,3,3,3; p=3: 1,1,2,2,2,2; p=5: 1,1,1,1,2; p=7: 1.
Exact linear algebra mod p^(v+k), cross-checked by exhaustive search; smaller Z excluded only for v <= 8 (the proof
covers all v). Recurrence range and full periodic range agree in 1060 cases; 20 small exhaustive cases agree.
Theorem B: exhaustive (p = 2, 3, 5) and linear algebra (p = 2, 3, 5, 7, Z from p to 4p), no violations.
Constructions: every n <= 10^5 plus (H9), (H10) at every x <= 10^5 and moment conditions for all r: 43 of 43 pass;
all nine coefficient rows match. H7 for z = -10..20, n <= 10^5. d_2(12) - d_-2(12) = 8 confirmed; B_2 - B_-2 works.
Caveat: n <= 10^5 has omega(n) <= 6, so for larger node sets the moment check is the real test.
Theorem A slice formula over Z[i] with characters, power shifts, inverse factors, squarefull terms: 2240 checks, 0 fail.

## 5. Comparison with our mu result
Same Kempner shape, different mechanism (sum of v_p over nodes here; K0 + v_p(K0!) there). The relation between
S(p^k) here and L(p, k) = S(p^k) - 1 for mu (indexing shift or not) was not checked. No claim.

## Least sure (for the verifier)
1. Definition of D_k (not stated in the extract). 2. The unstated O cap Q = Z step. 3. Signed degree as the complexity
measure. 4. The fixed-v pattern (computed only). 5. S(p^k) versus L(p, k) = S(p^k) - 1.
