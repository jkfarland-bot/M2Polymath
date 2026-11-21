# Claims, sources, review status and Lean certification

Every result in this repository, where it came from, how it was checked, and which Lean theorem (if any) certifies it.
Status words: **proved (Lean)** means a kernel-checked theorem in `lean/` on the standard axioms only
(propext, Classical.choice, Quot.sound); **proved (paper)** means a written proof checked by at least two independent
reviewers (worker and verifier, or worker and cold reader); **computed** means exact integer computation over a stated
range; **conditional** means it depends on unreviewed external work and is not claimed here.

Sources: **ours (R-113)** = J.S. with Claude, 9 Nov 2026; **A19** = an answer by ChatGPT (OpenAI) to our question Q19,
9 Nov 2026; **Claude seats** = Claude (Anthropic) agents in the review of 20 Nov 2026. Review reports are in `reviews/`,
check code in `code/`, ledger entries in `ledger/`.

| Result | Statement (short) | Source | Status | Lean (module: theorem) |
|---|---|---|---|---|
| Slice reduction (Theorem A) | On squarefree n whose primes are all 1 mod M, every member of the family is sum_z a_z z^omega(n) mod p^m | ours (R-113); A19 extended it | proved (Lean), over Z and over rings of integers | Slice: fam_slice; FamGen: famI_slice; RingO: famO_slice |
| O1 (Corollary A1) | No member detects primes mod p (weakest target) | ours (R-113) | proved (Lean) | A1: corA1_I, not_targetU_I; RingO: corA1_O; TwistO: corA1_twistedO |
| O2 and Theorem B | The divided target needs an active degree z with v_p(z) = 1; degree p needed; mod 9 condition; Vandermonde variant | O2 ours (R-113); exact form A19 | proved (Lean) | Moment: thmB_moment; Slice: thmB_arith; BCor: thmB_degree_p, not_targetD_below_p, mod9_I, mod9_iff, vandermonde_I |
| Theorem H (exact degree) | Least degree for pi(x) mod p^k: S(p^ceil(k/2)) signed, S(p^k) cheap (Kempner S) | A19 | proved (Lean), iff over Z and over every ring of integers incl. Z[zeta_N], Z_p | MomentZ: cheap_moment_iff; Construct: Zcheap_eq, Zsigned_eq; FamGen: ZcheapI_eq; M2ConstructO: ZcheapO_eq, Z_cyclotomic_eq |
| (H5) to (H10) | Lagrange weights, tables, squarefull lifts, prime-counting identities | A19 | proved (Lean) | M2Tables: rows_positive, rows_signed, level_table_isLeast, H7_series; Construct: core_mul_hcorr; Summatory: H9_H10 |
| Twisted factors | Dirichlet characters, power twists; slice congruence on primes 1 mod p^m times levels | A19 (model); Claude seats (Lean) | proved (Lean) | Twist: core_congr, thmH_twisted; TwistO: thmH_twisted_cyclotomic; M2ConstructO: chi4_isGreatest |
| Link to the Mobius level count (R-053) | H's moment argument gives L + 1 >= S(p^k) for mu | Claude seats (M2a-v, cold read) | proved (Lean) | MuShift: mu_moment_kempner, levelCount_zetaZ_via_H |
| Theorem D | Unequal-shift filters (F = 3A - 2B mod 9, F = 2A - B mod 4) give pi(x) mod 3 and parity; they refute our Q2.2, Q2.3 conjectures only as literally worded. With the Q2.2 twist condition required only at primes q != 3, the mod 9 filter is inside the conjectured class, so restated Q2.2 is open | A19 (filters); Claude seats (the q = 3 analysis) | proved (Lean) | M2FilterD: thmD_mod9, thmD_mod4, thmD_model_mod9; M2Closures: F9_not_ConjClass; Audit.AuditR5: DType3_iff_d3, F9_in_relaxed |
| Theorem E | One S3 cubic core cannot be repaired inside the family (M must include p^m) | A19 | proved (paper) (uses Chebotarev) | none |
| Theorem G | Gap in Lelechenko arXiv:1305.1639 Theorem 5 (page 9 step); printed 9/23 invalid, safe 3/5 (5/9 with faster D_3); Example 14 also affected; his Theorem 2 (7/15) stands | A19 (gap); Claude seats (Example 14) | proved (paper); the failing step proved (Lean) | M2GapG: lelechenko_step_fails, printed_bound_fails |
| Theorem J | Linear class-number-3 theta filters fail | A19 | algebraic core proved (Lean) under stated theta and Chebotarev hypotheses; full statement proved (paper) | M2ThetaJ: thetaJ_no_filter; M2ThetaJ2: thetaJ_slice, thetaJ_denominator, thetaJ_principal |
| Theorem K | No pointwise detector of primes a^2 + 27b^2 inside the family (M must include 2^m) | A19 | proved (paper); witness pairs proved (Lean) | M2WitnessK: K_witness_* |
| Theorem L | Parity of #{q = a^2 + 27b^2} from a primitive-norm count, x^(1+o(1)) | A19; (N2) in Lean by Claude seat M2L6n | proved (Lean), all parts, unconditionally (v1.2.0); compared on Palomar since v1.3.0 | M2TheoremL: Wfun_eight_dvd, L_N3; N2: Wfun_prime_pow, L_summed_exact_Wfun, L_summed_mod8_Wfun, L_N3_Wfun |
| Section 7 (F1) and (M1) | D_3(x) = floor(x^(1/3)) + 3H(x); the symmetric ternary count | A19 | proved (Lean) | M2Ternary: ternary_F1, ternary_M1 |
| Result M | pi(x) mod 3 below square root iff D_3(x) mod 9 below square root | A19 | identities and both reductions proved (Lean); cost accounting proved (paper) | M2Polymath: S3_mod_nine; M2ResultM: primeCounting_M3, primeCounting_M4, piMod3OfD3_correct, D3mod9OfPi_correct |
| Result N | Positive tuple count for the mod 3 output; (N4), (N5) | A19 | proved (Lean); circuit-size bound proved (paper) | M2ResultN: N4, N4_pointwise, N4_first_failure; M2TupleN: cL_count, TT_eq, N5 |
| D_3 in x^(5/9) | D_3(x) exactly in O(x^(5/9) log^2 x) operations, unconditionally; so pi(x) mod 3 in x^(5/9+o(1)) | Claude seats (M2e proof, M2e-v cold read); method after Polymath4 section 2.1 | cost proved (paper): PROOF_D3_5_9.md; the algorithm proved correct (Lean) for every input; the per-call cost of the incomplete sums proved (Lean, v1.2.0) in an explicit operation-count model, uniformly in L; the sum over a is a paper proof | M2BlockS: blockS_eq, D3fast_eq, piMod3_correct; M2AxisSwap: axis_swap; CostAll: approx_good, blockStep_checks, nblocks_le, blockSZW_fst, blockSZW_cost |
| Gap in Sladkey's T_3 claim | arXiv:1206.3369 section 8 gives no routine for an arbitrary lower limit; the naive finish is x^(2/3) | Claude seats (M2d, M2d-v) | computed and read | none |
| Hull-walk routine | Faster incomplete-sum routine (about 4x) | Claude seat (M2d-v) | correct (computed); cost empirical | none |
| Section 9 parity | x^(5/11) parity (Croot 2009); identities (P1), (P2) | Croot; A19 | (P1), (P2) proved (Lean); the bound depends on a fast D_2 and HKM Theorem 5 | M2Parity: P1, P1_real, S2_exact, P2 |
| Remarks of A19 (H6 link, finite domain, F_{p^2}) | (H6) equals the correction values; Theorem B fails on a finite domain without degree p; f^(*p) != E_p(f) over F_{p^2} | A19 | proved (Lean) | M2Closures: hcorr_prime_pow_eq_H6, thmB_finite_domain, Fp2_counterexample, rows_H9_H10, thetaJ_multi, chi4Member_targetDO_cyclotomic |
| Frobenius identity | f^(*p) = E_p(Frob o f) in characteristic p | A19 remark | proved (Lean) | M2Frobenius: frobenius_dirichlet |
| Result O | pi(x) mod 3 in x^(1/3+o(1)) | A19, via an unreviewed ETH-refutation preprint and Tulsyan arXiv:2611.00116 | conditional, external; not claimed | none (A19's own Lean for it was not built) |
| 47/104 parity | From Li arXiv:2609.29949 | A19 | conditional, external; not claimed | none |

Prior art for context: Polymath4 (Math. Comp. 81 (2012), arXiv:1009.3956) has the sufficiency direction (D_3 mod 9 gives
pi mod 3; Tao, Research Thread III, Aug 2009); Croot's note of 28 Aug 2009 (x^(5/11) parity); Sladkey arXiv:1206.3369;
Lelechenko arXiv:1305.1639; Lagarias and Odlyzko 1987; Hirsch, Kessler and Mendlovic arXiv:2212.09857. "No prior art
found" in reviews/b_REPORT_M2b.md is never a claim of novelty.
