# Seat M2L4-v: statement audit of m2/lean4 (20 Nov 2026). Saved by the director from the seat's returned text.
Audit file m2/lean4_audit/Audit4.lean (exit 0); negative control Neg.lean (decide refutes rStar 28 = 5).
Director rebuild m2/lean4_dir_rebuild: 8 files exit 0, no warnings, 378 declarations, standard axioms only; worker: 67 main theorems standard, 8 of 8 planted errors fail.
M2ResultM FAITHFUL: iroot = real floor of x^(1/k); (M3), (M4) exact over Z for every x (stronger than extract); H_mod_three second
transform for every x; recovery via representative in {0,3,6}; oracle reductions query only y <= x, outputs (pi x : ZMod 3) and
D3 x % 9, instantiated with true oracles; S3_I2 = (I2) at p = 3.
M2AxisSwap FAITHFUL WITH CAVEATS: truncated M - r needed (untruncated fails at y = 1, a = 1; decide); matches hull.py's c < r guard;
D3_eq_F1_swap exact; Stern-Brocot walk not formalized.
M2ConstructO FAITHFUL WITH CAVEATS: iff and IsLeast over char-0 domains with IntDvdDescends (rings of integers, Z[zeta_N], Z_p);
untwisted cores in the iff; chi4 core = id * chi4, signed degree 2, q + chi4(q) == 2 mod 4 (core(3) = 2, core(5) = 6);
chi4_isGreatest: k = 1 = v_2(2), equality in (H4) for a twisted core; member over Z (TargetDO version follows, not stated).
M2Tables FAITHFUL WITH CAVEATS: 9 rows and 16 Kempner cells match section 11 entry by entry (kernel decide); rows are Lagrange
weights (uniqueness); (H6), (H7) as power series over Z; series not linked to round 1 hcorr.
M2ThetaJ2 FAITHFUL WITH CAVEATS: denominators 2^e 3^t; principal variant; (T1) and split values hypotheses; toy model;
single correction h (multi-correction reduction not stated).
M2ResultN FAITHFUL: c_0 = delta, c_{L+1} = d_2 * E_3(c_L); N4 over ZMod 3; pointwise 1 <= n < 2^(3^L); first failure +1 at 2^(3^L).
M2TheoremL FAITHFUL WITH CAVEATS: rStar, Wfun exactly (N1); Wfun_one, four_dvd_rStar, Wfun_eight_dvd unconditional;
L_summed_exact, L_summed_mod8, L_N3 (exactly (N3)) conditional on (N2) (hWpp); R abstract; (N2) not proved.
M2Frobenius FAITHFUL: f^(*p) = E_p(Frob o f) for CharP R p; F_{p^2} counterexample not formalized.
Not covered (whole M2 Lean): all costs ((F1), (F2), (M5), Result M complexity, hull walk, (N6), x^(5/11), 47/104, (G2)); (P1),
(P2); Result N tuple count, T_{j,L}, (N5), circuit size, F_3[[t]] form; Theorem L (N2), R, cubic-residue criterion; Theorem J
(T1), eta, Chebotarev, multi-correction reduction; Theorems C, E, K F-side; HKM Theorem 5; (H6) link to hcorr; (H9), (H10) with
table weights; fixed v; general localizations; twisted iff over O; TargetDO member with nontrivial character; B finite-domain
remark; converse of mu shift; F_{p^2} counterexample; (I2) general p, (I3) to (I5), (S1), (S2); section 9c; D's meta-claim.
