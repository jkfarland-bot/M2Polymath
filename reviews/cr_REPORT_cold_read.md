# Cold read: mu to cheap D_k slice reduction (R-053 lower bound via Theorem H), 20 Nov 2026
Saved by the director from the seat's returned text. Script: m2/cr/check_mu_shift.py (python3 -I, exact).

VERDICT: HOLDS WITH FIXES (notation and citation; conclusion L >= S(p^k) - 1 unchanged).
1. E_p part: for squarefree n a divisor m^p is squarefree only if m = 1, so (zeta^{*z} * E_p(g_z))(n) = g_z(1) z^omega(n),
   c_z = g_z(1), z = 0 gives c_0 [r = 0]. Any squarefree n works; the condition "primes 1 mod M" is not needed.
2. Shift: zeta * mu = delta; multiplying by integral zeta keeps the congruence; moments sum_z c_z (z+1)^r == [r = 0].
3. Notation: b_w := c_{w-1} on nodes w in 1..L+1, a_w := b_w D / w (not c_w D / w).
4. a_w integral (every w | D). 5. s_r = D sum_w b_w w^(r-1): s_1 = D(1 + p^k m), s_r in D p^k Z for r >= 2; v = v_p(D),
   prime value p^v times a unit, composites v_p >= v + k: the D_k target holds.
6. Cite H's moment lemma (H3)-(H4), not the full-function Theorem H; H8 gives a full lift F = sum a_w B_w if wanted.
7. Simpler: Q(t) = prod over w with b_w != 0 of (t - w); 0 = sum b_w Q(w) == q_0 mod p^k, q_0 | (L+1)!, so
   k <= v_p((L+1)!), L + 1 >= S(p^k). No D or v needed.
8. Converse ("different statements") plausible, not checked in depth; no effect on the lower bound.
Script: step 1 brute force (p = 2, 3, z = 0..3, n <= 210); binomial identity (200 random vectors, r < 60); all solutions
mod p^k of sum c_z z^r == (-1)^r enumerated (p = 2, k = 1..4; p = 3, k = 1, 2; L <= 6, p = 2 k = 4 only to L = 4);
thresholds exactly L = S(p^k) - 1 (p = 2: 1, 3, 3; p = 3: 2, 5); all checks pass.
