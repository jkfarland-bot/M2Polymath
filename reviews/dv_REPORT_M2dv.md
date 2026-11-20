# Seat M2d-v report: verifier for M2d, and the x^(5/9) question (20 Nov 2026)

Saved by the director from the seat's returned text. Scripts in m2/dv/ (hull.py, t_hull_correct.py, t_hull_cost.py,
t_F1_fast.py, t_F1_sampled.py, fit.py, check_MLN.py, check_M_large.py; each with .out; python3 -I, exact integers).
Sladkey read as full extracted text (sections 2 to 9).

## 1. x^(5/9): ESTABLISHED WITH OUR FIX (cost bound measured, not yet proved)
(a) Confirmed: Sladkey's sweep starts at floor(sqrt n), descends through integer-slope bands ending at
x4 = floor(sqrt(n/a1)), stops when x4 < x_min and finishes [x_min, x2) column by column. Section 8's "partial result"
claim holds only for x1 <= x_min (about z <= n^(1/4) in T_3); section 9 notes the issue but gives no procedure (states
O(n^(5/9 - c + eps)) and O(n^(1/2) log n) only "if we could prove G = 1/2"). Band-then-columns costs about
sum_a a^4/(4x) = x^(2/3)/20 (worker measured 0.049 x^(2/3)): Theta(x^(2/3)); full D_2 oracle minus prefix also
Theta(x^(2/3)). A19's "Sladkey's interval routine costs O~(y^(1/3))" overstates the source.
(b) Fix: y = floor(x/a), r = isqrt(y), c = min(max(a-1, floor(y^(1/3))), r), M = floor(y/(c+1)):
  sum_{a<=b<=r} floor(y/b) = sum_{a<=b<=c} floor(y/b) + r(r-c) + sum_{r<t<=M} floor(y/t) - c(M-r)
(exact axis swap; rows above sqrt y counted as columns). The last sum starts at abscissa r (slope <= 1), stops at
M <= y^(2/3), and is evaluated by a Stern-Brocot convex-hull walk over lattice points just outside the hyperbola,
leftover columns direct (at most y^(1/3)).
Correctness vs brute force: every N <= 3000 with every L (111,099 cases), random N to 10^12 (3,965), squares, k(k+1),
cubes and +-1 neighbours (13,946), N about 10^13 to 10^14 (12): 0 failures. D_3 by (F1) with the routine matches a d_3
sieve for every x <= 30,000 and every 97th to 3 * 10^5, an independent grouped sum_a D_2(x/a) at 10^7, 10^8 + 7,
10^9 + 7, 10^10; D_3(10^6) = 106,030,594.
Cost per call (steps / N^(1/3)): L = 0 grows like 1.2 ln N (16.1 at 10^6, 50.2 at 10^18); at N about 10^18: 50.2, 49.2,
30.9, 15.8, 3.2 for L = 0, N^(1/3), N^0.4, N^0.45, N^0.49: uniform in L, about y^(1/3) log y.
Total (F1) steps: 10^9 1.60e6 (16.0 x^(5/9), 1.60 x^(2/3)); 10^11 2.30e7 (17.8, 1.07); 10^13 3.219e8 (19.3, 0.69);
10^15 4.44e9 (20.6, 0.44); 10^17 5.84e10 (21.0, 0.27); 10^19 8.03e11 (22.3, 0.17). Exact to 10^13, stratified samples
after (sample at 10^13 within 0.01% of exact; s.e. about 1.5%). Fitted exponent 0.569 (all), 0.566 (x >= 10^13); after
dividing by ln x, 0.537: between x^(5/9) and x^(5/9) log x, far from 2/3. End to end pi(x) mod 3 via Result M with this
oracle correct at 10^9 + 7, 10^10, 10^11 (pi(10^11) = 4,118,054,813, residue 2), about 35 x^(5/9) steps.
Not proved: the walk's y^(1/3) log y bound (measured uniformly in L). Published sketched rigorous substitute: Polymath,
Math. Comp. 2012 section 2.1 (arXiv:1009.3956): sum_{A<=n<2A} floor(x/n) in x^(1/3+o(1)) by blocks starting at any
n0, handling any lower limit above 100 y^(1/3).
(c) Other unconditional D_3 algorithms below x^(2/3): Lelechenko arXiv:1305.1639 Theorem 3 with Example 12
(d_3 = d_2 * 1): 3/5 + eps, needing full D_2 at x^(1/3 + eps) (the A19 gap concerns his Theorem 5, not Theorem 3).
Polymath section 4: 2/3 - c. HKM 2212.09857: no D_3 routine (Theorem 5: Mertens in O(sqrt N log^2 N)). Tudzi
arXiv:2607.10053: analytic error bounds only. Nothing else found; Li not relied on.

## 2. Result M: CONFIRMED
Own code, every x <= 3 * 10^4, zero failures (M1 pointwise and prefixes, cube-root sum = 1, S_3 == 1 + 3G mod 9, both
(M2), (M3), (M4) exact, both reductions as algorithms; d_3 from factorizations, h(n) from divisor pairs). Forward chain at
10^9 + 7, 10^10, 10^11; reverse gives D_3(10^9 + 7) mod 9 = 4, matching. Costs: forward x^(1/3) oracle calls, total
x^(max(alpha, 1/3)+o(1)); reverse adds e >= 2 calls totalling x^(1/3+o(1)). Fixed saving below 1/2 survives both ways.
Keep the wording fix "at least two".

## 3. Theorem L: CONFIRMED
-108 = 6^2 (-3), conductor 6; h = 1 * 6 / [O_K^* : O^*] * (1 + 1/2) = 3; reduced forms [1,0,27], [4,+-2,7]. (N2) from
p^j principal iff [p] = 1 or 3 | j, two generators each, two conjugates; inert primes have no primitive
representations. (N1), (N2) pointwise and summed mod 8 and (N3) for every n, x <= 3 * 10^4; 534 represented primes.

## 4. Result N and section 9: CONFIRMED in outline
N: c_L from local series; (N4) n <= 2 * 10^4, L <= 3; first failures against mu at 2, 8, 512; T_{j,L} vs literal tuples
(x < 1500, L <= 2); (N5) at least depth for every x <= 2 * 10^4.
Section 9 unconditional: (P1), (P2) as identities; exponent arithmetic; 9c algebra; the (1 + 2 beta)/3 bound given an
incomplete oracle. x^(5/11) needs D_2 in y^(1/3+o(1)) (Polymath 2.1 sketch, Sladkey's semi-formal G, or our walk,
measured) and HKM Theorem 5 (not checked internally); Croot's route needs only the D_2 input. 47/104 depends on Li
(unreviewed) and (G2). 9c per-shell bounds and (1 + log_3 2)/3 depend on Sladkey's G argument (draft-level).

## 5. Worker script audit: no circularity
Tables independent of tested identities. Limits: the x^(2/3) band figure is an analytic proxy; (N5) to 10^5 uses the
c_L/H convolution checked against literal tuples only to x <= 2000.

## Least sure
1. Walk cost bound empirical. 2. Polymath 2.1 is a published sketch. 3. HKM Theorem 5 not checked. 4. 10^15 to 10^19
totals are stratified estimates (s.e. about 1.5%).
