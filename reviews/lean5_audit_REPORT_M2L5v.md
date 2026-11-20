# Seat M2L5-v: statement audit of m2/lean5 (20 Nov 2026). Saved by the director from the seat's returned text.
Audit file m2/lean5_audit/Audit5.lean (no errors, three lints, standard axioms). Director rebuild m2/lean5_dir_rebuild: 4 files exit 0,
one unused-variable lint, 363 declarations, standard axioms only; #eval D3fast(10^6) = 106,030,594, 10^7 = 1,421,760,251,
10^8 = 18,362,473,634. Worker: 34 theorems printed (33 standard, bfirst_spec on propext and Quot.sound only); 4 of 4 planted errors fail.
M2BlockS FAITHFUL (correctness only): blockS_eq for all y, L, no hypotheses; run-time window checks fall back to direct sums and
blockStep_spec proves every branch equals the direct sum, so correctness never depends on them; checks match PROOF Lemma 3;
D3fast_eq for every x; piMod3_correct, piMod3_val unconditional. Fast path non-vacuous (#eval): 4,416 of 4,416 blocks at y = 10^9,
26,952 of 26,952 at y = 123456789012 (about 32% of the Lemma 7 bound). Cost not certified (Lemmas 2, 6, 7 not formalized as bounds).
M2Parity FAITHFUL: f2 = E2mu * tau = 2^omega; P1_general under U^2 V <= x < (U+1)^2 (V+1) (exact hyperbola conditions); P1 at
U = iroot 11 (x^4), V = iroot 11 (x^3) for every x (P1_real with real floors); S2_exact; P2 for x >= 1 (x = 0 correctly excluded).
M2Closures FAITHFUL WITH CAVEATS: hcorr_prime_pow_eq_H6 for every z, q, e; rows_H9_H10 = the same 10 (row, level) pairs as
round 4's rows_targetD (H9 modulus C p^k; H9_exact gives C prod z); thetaJ_multi (common S, e, t; satisfiable); chi4 TargetDO over
Z[i] and every O_{Q(zeta_N)} (real character: cast of a Z member; no non-real character); Fp2_counterexample matches; thmB_finite_domain
matches (F = -3B_1 + 3B_2 works for omega <= 2, fails at 30). DType3/ConjClass literal but degenerate: Audit5.DType3_iff_d3 proves
every DType3 core equals zeta^3 (the twist condition at q = 3 kills every k >= 1 and every nontrivial chi), so ConjClass = integral
combinations of d_3 * h_i; ConjClass_three a correct invariant; F9_not_ConjClass nearly trivial. With the twist condition only at
q != 3 (ConjClass'), Audit5.F9_in_relaxed proves the round 3 mod 9 filter IS in the class (via thmD_model_mod9). So the Lean
certifies only the literal refutation of Q2.2, not its spirit.
M2TupleN FAITHFUL: cL_count (tuple count, independent of N); TT exactly the extract's predicate; TT_eq for j >= 1; N5 under
icbrt x < 2^(3^L), weights (j mu(j)) % 3, for all x (stronger than x >= 2); N5_zmod.
Not covered after round 5: all costs (5/9 operation count, (F2), (M5), Result M complexity, hull walk, (N6), x^(5/11), 47/104, (G2),
circuit size); F_3[[t]] form of N; Theorem L (N2), R, cubic-residue criterion; Theorem J (T1), eta, Chebotarev; C, E, K F-side;
HKM Theorem 5; fixed v; general localizations; twisted iff over O; converse of mu shift; non-real-character TargetDO member;
(I2) general p, (I3) to (I5), (S1), (S2); section 9c; the restated Q2.2 (q != 3, local factor == (1-t)^3) and its classification.
