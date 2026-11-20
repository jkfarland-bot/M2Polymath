# D_3(x) in O(x^(5/9) log^2 x) operations: full proof (seat M2e, fixes from cold reader M2e-v applied), 20 Nov 2026

Model: arithmetic operations (+, -, *, floor division, comparison) on integers of O(log y) bits; "ops" counts these.
Code: code/e/blocksum.py (worker), code/ev/hs.py (independent implementation by the cold reader from this text).

## Routine S(y, L) = sum_{L < b <= r} floor(y/b), r = isqrt(y), 0 <= L, c0 = icbrt(y)
1. Direct columns: for b from L+1 to min(c0, r) add floor(y/b). Set n0 = max(L+1, c0+1).
2. Blocks, while n0 <= r: R = r - n0 + 1; Q = icbrt(floor(n0^3/y)); (a, q) the last continued-fraction convergent of
   y/n0^2 with q <= Q. If R < q add the remaining terms directly and stop. Otherwise k = floor(min(Q, R)/q), H = kq,
   s = floor(qy/n0). The block sum over n0 <= n < n0 + H is the linear sum (Lemma 4) plus a correction for each class
   j in J = {0, q-2 mod q, q-1 mod q} (Lemma 5). Set n0 = n0 + H.

## Lemmas
**Lemma 1 (expansion).** For integers n0 >= 1, t >= 0, n = n0 + t, alpha = y/n0^2: y/n = y/n0 - alpha t + y t^2/(n0^2 n).
Proof: multiply 1/n0 - t/n0^2 + t^2/(n0^2(n0+t)) by n0^2(n0+t): n0(n0+t) - t(n0+t) + t^2 = n0^2.

**Lemma 2 (convergents).** For positive integers u, v and Q >= 1, the Euclidean algorithm on (u, v), stopped at the first
convergent with denominator above Q, returns coprime a, q with 1 <= q <= Q and |u/v - a/q| < 1/(qQ) (or = 0), in at most
log_phi(Q) + 3 division steps. Proof: q_0 = 1 <= Q, so a valid convergent exists (never None). Consecutive convergents
satisfy p_k q_{k-1} - p_{k-1} q_k = +-1, so they are coprime (Hardy and Wright Thm 150). If p_k/q_k is not the last
convergent, u/v - p_k/q_k = (-1)^k/(q_k(a'_{k+1} q_k + q_{k-1})) with complete quotient a'_{k+1} >= a_{k+1}, so the
denominator is at least q_k q_{k+1} (Hardy and Wright section 10.7); as q_{k+1} > Q the error is below 1/(q_k Q). If it is
the last convergent the error is 0. Steps: q_k >= F_{k+1} >= phi^(k-1), so the first K with q_K > Q has K <= log_phi Q + 2.
When alpha >= 1, a >= 1.

**Lemma 3 (error window).** Assume Q >= 1, Q^3 y <= n0^3, (a, q) from Lemma 2 with u/v = y/n0^2, and 0 <= t < H <= Q.
Let E(t) = y/n - (qy/n0 - at)/q. Then -1/q < E(t) < 2/q. Proof: by Lemma 1, E = E1 + E2 with E1 = -(alpha - a/q)t,
E2 = y t^2/(n0^2 n). |E1| <= t/(qQ) < H/(qQ) <= 1/q (strict since t <= Q - 1). 0 <= E2 <= y t^2/n0^3 < y Q^2/n0^3 <= 1/Q
<= 1/q using Q^3 y <= n0^3 (strict for t < Q; E2 = 0 at t = 0). In the routine Q = icbrt(floor(n0^3/y)) gives
Q^3 <= floor(n0^3/y) <= n0^3/y, and n0 >= c0 + 1 > y^(1/3) gives Q >= 1.

**Lemma 3' (classes).** Write qy/n0 = s + phi with 0 <= phi < 1, g(t) = (s + phi - at)/q, j(t) = (s - at) mod q. Then
floor(g(t)) = (s - at - j(t))/q and frac(g(t)) = (j(t) + phi)/q; if 1 <= j(t) <= q-3 then floor(y/n) = floor((s - at)/q).
Proof: with N = s - at = qF + j, (N + phi)/q = F + (j + phi)/q and (j + phi)/q in [0, 1). y/n = g + E, so
floor(y/n) = floor(g) + floor(frac(g) + E). By Lemma 3, frac(g) + E lies in ((j + phi - 1)/q, (j + phi + 2)/q), contained
in ((j-1)/q, (j+3)/q) since 0 <= phi < 1; for 1 <= j <= q-3 this is inside [0, 1), so the second floor is 0. Both
boundaries j = 1 and j = q-3 are tight. J = {0, q-2, q-1} is exactly the complement. For q <= 3 the set J (deduplicated:
{0} for q = 1, {0, 1} for q = 2, {0, 1, 2} for q = 3) is every class, so correctness there rests on Lemma 5 alone.

**Lemma 4 (linear part).** If gcd(a, q) = 1 then sum_{t=0}^{kq-1} floor((s - at)/q) = ks - aqk(k-1)/2 - k(a+1)(q-1)/2.
Proof: t = qi + u, 0 <= u < q: floor((s - at)/q) = -ai + floor((s - au)/q). As u runs over [0, q) the residues
(s - au) mod q run over [0, q) since a is invertible mod q, so sum_u floor((s - au)/q) = (qs - aq(q-1)/2 - q(q-1)/2)/q.
Sum over i < k. (If q is even then a is odd, so (a+1)(q-1)/2 is an integer.)

**Lemma 5 (exceptional classes).** Fix rho in [0, q); m = n0 + rho, f = floor((s - a rho)/q), F_l = floor(y/(m+ql) + al),
0 <= l < k. Then floor(y/(m+ql)) = F_l - al; F_l in {f-1, f, f+1, f+2}; sum_l F_l = k(f-1) + sum_{T=f}^{f+2}
#{l : (T - al)(m + ql) <= y}. The class correction is (k(f-1) + counts - ak(k-1)/2) - (kf - ak(k-1)/2). The classes needed
are rho = a^(-1)(s - j) mod q for j in J; every other class contributes exactly its linear part by Lemma 3'; |J| <= 3.
Proof: al is an integer, so floor(y/n + al) = floor(y/n) + al. g(rho + ql) = g(rho) - al, so y/n + al = g(rho) + E with
f <= g(rho) < f + 1; by Lemma 3 this lies in (f - 1/q, f + 1 + 2/q), inside (f-1, f+3). F_l = (f-1) + sum_{T=f}^{f+2}
[F_l >= T], and F_l >= T iff y/n >= T - al iff y >= (T - al) n since n > 0. Since H = kq, t = rho + ql covers the class
exactly. (F_l = f+2 can occur only when q <= 2.)

**Lemma 6 (concave counting).** P(l) = (T - al)(m + ql) has second difference -2aq <= 0, so {l in [0, k-1] : P(l) > y} is
an interval (possibly empty); count_ge finds its size with at most 4 ceil(log2 k) + 1 evaluations of P. Proof:
Delta(l) = P(l+1) - P(l) is nonincreasing; with l* the least l with Delta(l) <= 0 (or k-1), P is nondecreasing on [0, l*]
and nonincreasing on [l*, k-1], so the superlevel set is an interval containing l* when nonempty. The argmax search is a
binary search on a monotone predicate (at most ceil(log2 k) iterations of 2 evaluations), plus 1 evaluation at l*, plus two
one-sided searches of at most ceil(log2 k) evaluations each.

**Lemma 7 (block count).** Let c = y^(1/3) and N1 = max(L+1, c0+1) > c.
(a) Every block has Q >= 1, q <= Q, k >= 1 and H <= min(Q, R). (n0 > c gives n0^3 > y so Q >= 1; blocks are formed only
when R >= q.)
(b) If R >= Q then H >= Q/2 >= n0/(4c). H = q floor(min/q) >= max(q, min - q + 1) >= min/2. For Q >= n0/(2c): from
(Q+1)^3 > n0^3/y, Q > n0/c - 1. Case n0/c >= 2: Q > n0/c - 1 >= n0/(2c). Case 1 < n0/c < 2: Q >= 1 > n0/(2c).
(c) While R >= Q each block start satisfies n_{i+1} >= n_i (1 + 1/(4c)) and starts stay <= r; since
1/ln(1 + u) <= (1 + u)/u, the number of such blocks is at most 1 + (4c + 1) ln(r/N1), with r/N1 <= y^(1/6).
(d) Q is nondecreasing in n0 (icbrt of a monotone floor) and R strictly decreases, so the phase change to R < Q is one-way.
From then on H >= R/2, so R at least halves per block; since R < Q <= y^(1/6) (Q^6 <= y), at most log2(y^(1/6)) + 1 such
blocks follow, then fewer than q <= y^(1/6) direct terms.

## Key Lemma
For every y >= 1 and every 0 <= L <= isqrt(y), the routine returns S(y, L) exactly using O(1 + y^(1/3) log^2(y+2)) ops,
uniformly in L, on integers of O(log y) bits. Proof: the blocks partition [N1, r] and each block sum is exact by Lemmas 3',
4, 5, 6. Direct columns: at most y^(1/3) divisions. Per block: one icbrt, O(log y) ops by bisection or Newton; continued
fractions at most log_phi Q + 3 steps (Lemma 2); the modular inverse a^(-1) mod q, O(log q) by extended Euclid (also free
from the previous convergent since a q' - p' q = +-1); counting at most 9(4 ceil(log2 Q) + 1) evaluations (Lemma 6). Total
O(log y) per block, within O(log^2 y). Number of blocks by Lemma 7: at most 1 + (4 y^(1/3) + 1)(ln y)/6 +
log2(y^(1/6)) + 1. L enters only through N1 >= c0 + 1. Sizes: n0^3 <= y^(3/2); |T - al| <= y + 3 + aQ with
a <= (y/n0^2)Q + 1; m + ql <= 2 sqrt(y); the overshooting convergent in Lemma 2 has p up to about 4 y^(3/2): all O(log y) bits.

## Theorem
D_3(x) can be computed exactly in O(x^(5/9) log^2 x) arithmetic operations on O(log x)-bit integers, i.e.
O(x^(5/9) (log x)^2 M(log x)) bit operations: O(x^(5/9) (log x)^3 log log x) with Harvey and van der Hoeven multiplication,
O(x^(5/9) (log x)^4) with schoolbook multiplication.
Proof: (F1) (certified in Lean: M2Ternary.ternary_F1): D_3 = 6B - 3E_ab - 3E_bc + m. The nested floor identity
floor(floor(x/a)/b) = floor(x/(ab)) turns the inner sum of B into S(floor(x/a), a-1) - sum_{b=a}^{h_a}(b-1), where the
subtracted sum is h_a(h_a - 1)/2 - (a-1)(a-2)/2. Valid lower limit: a <= m = icbrt(x) gives a^3 <= x, so
a^2 <= floor(x/a), so a <= h_a and L = a - 1 <= isqrt(floor(x/a)). Inner sums: sum_{a<=m} C (x/a)^(1/3) log^2 x <=
C x^(1/3) (3/2) m^(2/3) log^2 x <= (3/2) C x^(5/9) log^2 x, using a^(-1/3) <= integral of t^(-1/3) over [a-1, a] and
m^(2/3) <= x^(2/9). Boundary terms E_ab, E_bc, m and per-a overhead (isqrt, icbrt, O(1) arithmetic): O(x^(1/3) log x).
D_3(x) <= x(1 + ln x)^2 has O(log x) bits.

## Evidence
Worker (code/e): every y <= 3000 with every L (111,099 cases), 7,500 random y <= 10^9 with all inequalities asserted in
exact rationals, 1,647 special forms to 2 * 10^10, 120 cases in [10^11, 10^13]: 0 failures; (F1) with the routine matches a
d_3 sieve for every x <= 30,000, D_3(10^6) = 106,030,594, matches the hull walk at 42 values to 10^10; blocks at 31 to 32%
of the Lemma 7 bound; Lemma 2 and Lemma 6 bounds attained exactly. Cold reader (code/ev, own implementation from this text):
every y <= 2000 with every L (62,674 cases) and 3,000 random y <= 10^7 fully instrumented (about 1.17M blocks), 10,500
cases to 10^10 and 11.3M instrumented blocks in [10^9, 10^10], special forms: 0 failures; D_3 via (F1) matches a sieve
for every x <= 20,000.

## Credits and prior art
Method: block decomposition in the style of Vinogradov and Polymath4 (Math. Comp. 2012, arXiv:1009.3956, section 2.1,
a sketch whose length-kq extension is unproved; Lemmas 5 and 6 close it). Sladkey arXiv:1206.3369 section 8 states
O(n^(5/9)) for T_3 but gives no procedure for an arbitrary lower limit. Proof by Claude (seat M2e), cold read by Claude
(seat M2e-v). Not used: the ETH-refutation preprint, Tulsyan, Li.
