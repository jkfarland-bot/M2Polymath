# Seat M2e report: D_3(x) in O(x^(5/9) log^2 x) operations, rigorous proof (20 Nov 2026)
Saved by the director from the seat's returned text (verbatim structure; full lemma text below).

## 0. Verdict and route
Theorem and Key Lemma proved unconditionally with explicit counts, Route B (block decomposition, Vinogradov / Polymath
section 2.1 style, every step exact). Route A (hull walk) still unproved: Balog and Barany arXiv:2602.06897 Thm 1.1
gives f_0(I(H_N)) of order N^(1/3) log N (vertex count) but not per-vertex search cost nor restriction to [r, M].
Route C: Helfgott and Thompson arXiv:2101.08773 do not prove the Key Lemma (for sum tau they cite [TCH12]).
Polymath 2.1 is a sketch: "all but O(1) values of r" on blocks of length q; the extension to length kq is unproved;
Lemmas 5, 6 close it. Model: arithmetic ops on O(log y)-bit integers.

## 1. Routine S(y, L) = sum_{L < b <= r} floor(y/b), r = isqrt(y), c0 = icbrt(y)
Direct columns b = L+1..min(c0, r); n0 = max(L+1, c0+1). While n0 <= r: R = r - n0 + 1, Q = icbrt(floor(n0^3/y));
(a, q) last convergent of y/n0^2 with q <= Q; if R < q add the rest directly and stop; else k = floor(min(Q, R)/q),
H = kq, s = floor(qy/n0); block sum over n0 <= n < n0 + H = linear sum (Lemma 4) + corrections for classes
j in J = {0, q-2 mod q, q-1 mod q} (Lemma 5); n0 += H. Code m2/e/blocksum.py (CHECK=True asserts every inequality).

## 2. Lemmas
L1 (expansion): n = n0 + t, alpha = y/n0^2: y/n = y/n0 - alpha t + y t^2/(n0^2 n).
L2 (convergents): Euclid on (u, v) stopped at the first denominator above Q gives coprime a, q, 1 <= q <= Q,
|u/v - a/q| <= 1/(qQ), at most log_phi(Q) + 3 steps (Hardy and Wright Thm 150, section 10.7).
L3 (error window): Q >= 1, Q^3 y <= n0^3, 0 <= t < H <= Q, E(t) = y/n - (qy/n0 - at)/q: -1/q < E < 2/q
(|E1| <= t/(qQ) < 1/q; 0 <= E2 <= y t^2/n0^3 < y Q^2/n0^3 <= 1/Q <= 1/q).
L3' (classes): qy/n0 = s + phi; j(t) = (s - at) mod q; frac(g) = (j + phi)/q; for 1 <= j <= q-3,
floor(y/n) = floor((s - at)/q).
L4 (linear part, gcd(a,q) = 1): sum_{t<kq} floor((s - at)/q) = ks - aqk(k-1)/2 - k(a+1)(q-1)/2.
L5 (exceptional classes): rho in [0,q), m = n0 + rho, f = floor((s - a rho)/q), F_l = floor(y/(m+ql) + al):
floor(y/(m+ql)) = F_l - al; F_l in {f-1..f+2}; sum_l F_l = k(f-1) + sum_{T=f}^{f+2} #{l : (T - al)(m+ql) <= y};
classes needed rho = a^{-1}(s - j) mod q, j in J, |J| <= 3.
L6 (concave counting): P(l) = (T - al)(m + ql), second difference -2aq <= 0; {l : P(l) > y} an interval; size found
with at most 4 ceil(log2 k) + 1 evaluations.
L7 (block count): N1 = max(L+1, c0+1) > c = y^(1/3); (a) Q >= 1, k >= 1, q <= Q, H <= min(Q, R); (b) R >= Q implies
H >= Q/2 >= n0/(4c); (c) blocks with R >= Q at most 1 + (4c+1) ln(r/N1); (d) then at most log2(y^(1/6)) + 1 blocks and
at most y^(1/6) direct terms.
Key Lemma: for every y >= 1, 0 <= L <= isqrt(y), S(y, L) exact in O(y^(1/3) log^2 y) ops, uniformly in L;
intermediates |.| <= y^2.
Theorem: D_3(x) exactly in O(x^(5/9) log^2 x) ops on O(log x)-bit integers, i.e. O(x^(5/9) (log x)^3 log log x) bit
ops (Harvey and van der Hoeven) or O(x^(5/9) (log x)^4) (schoolbook). Via (F1); inner sums S(floor(x/a), a-1) minus a
closed form; a <= icbrt(x) implies a <= h_a (valid lower limit); sum_{a<=m} (x/a)^(1/3) <= (3/2) x^(5/9); boundary
terms O(x^(1/3) log x).

## 3. Checks (m2/e/*.py, *.out)
t_correct.py: every y <= 3000 with every L (111,099), 7,500 random y <= 10^9 with all assertions, 1,647 special forms to
2 * 10^10, 120 cases in [10^11, 10^13]: 0 failures. t_D3.py: (F1) matches a d_3 sieve for every x <= 30,000;
D_3(10^6) = 106,030,594; matches the M2dv hull walk at 42 values to 10^10; sum_a (x/a)^(1/3)/x^(5/9) = 1.460 to 1.4996.
t_cost.py: blocks at 31 to 32% of the Lemma 7 bound (8,749,475 vs 27,791,341 at y about 10^18, L = 0); 64 H^3 y >= n0^3
on 790,350 blocks; ops/y^(1/3) at L = 0: 46, 150, 276 at 10^6, 10^12, 10^18 (/ln^2 y: 0.238 to 0.161); uniform in L
(276, 114, 23 for L = 0, y^0.45, y^0.49). t_perblock.py (9,336,940 blocks): CF steps <= log_phi Q + 3 (attained);
evaluations <= 9(4 ceil(log2 k) + 1) (attained). Full (F1) ops: 5.88e6, 9.89e7, 1.56e9 at 10^9, 10^11, 10^13
(58.8, 76.6, 93.7 x^(5/9); / x^(5/9) ln^2 x: 0.137, 0.119, 0.104); about 3.7 to 4.9 times the hull walk's step count.

## 4. Unproved
Nothing in the Theorem or Key Lemma. The hull walk's bound remains empirical. The log exponent 2 is likely one too many.
## 5. Sources: arXiv:1009.3956 (section 2.1 read), arXiv:2101.08773 (sections 1.2, 4), arXiv:2602.06897 (Thms 1.1 to 1.3);
Hardy and Wright Thms 150, 171 (from memory; Lemma 2's proof self-contained). PDFs in m2/e/dl_ht, m2/e/dl_pm.
