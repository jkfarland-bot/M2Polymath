# Seat M2L-v: statement audit of the M2 Lean files (20 Nov 2026)
Saved by the director from the seat's returned text. Audit file: m2/lean_audit/AuditV.lean (EXIT 0 against lean_dir_rebuild/build).
Director rebuild: m2/lean_dir_rebuild (Moment, MomentZ, Slice, Construct exit 0, no warnings; 140 declarations scanned,
only propext, Classical.choice, Quot.sound). Worker planted errors: 4 of 4 fail (m2/lean/planted, logs/planted_*.log).
Definitions: kempner = least N with p^k | N! (Found.lean:321; kempner 2 2 = 4); (k+1)/2 = ceil(k/2), no off-by-one;
TargetD matches D_k (u_q may depend on q; value at 1 and higher prime powers free; v existential; not TargetD of 0);
zpowZeta faithful (mixed zeta^a mu^b = zpowZeta(a-b)); hcorr integral, supported on 1 and squarefull n, hcorr_one = 1,
core_mul_hcorr; equals (H6) by uniqueness, (H6) itself not formalized.
Verdicts: thmB_moment(_exists, _std) FAITHFUL (one r >= 2 with p(p-1) | r-1 suffices). thmB_arith(_exists, _zpow_exists)
FAITHFUL WITH CAVEATS (Z not O; one core per degree label; infinite prime set P and congruence of cores are hypotheses;
corrections need only be 0 mod p^2 on squarefree m > 1). thmH_moment, momentTarget_le FAITHFUL (stronger: vanishing only
for 2 <= r <= |T|+1). sum_val_cheap/signed FAITHFUL. exists_weights, construct_moment, momentTarget_of_dvd FAITHFUL
(adjugate weights, existence only). MomentTarget, cheap/signed_moment_iff, IsLeast forms FAITHFUL (k >= 1).
fam_slice(_exact) FAITHFUL WITH CAVEATS (Z, one core per label). thmH_arith FAITHFUL WITH CAVEATS (as thmB_arith).
thmH_arith_zpow, cheap/signed_arith_lower FAITHFUL (broader correction class, so stronger). construction_explicit FAITHFUL.
cheap/signed_arith_iff, Zcheap_eq, Zsigned_eq FAITHFUL WITH CAVEATS (untwisted Z family; degree-0 terms excluded,
harmless but not formalized; squarefull-only version follows by combination, not one theorem; TargetD weakest target,
strong form via construction_explicit).
Non-vacuity (AuditV.lean): fam {2} 1 zpowZeta hcorr = B_2 meets TargetD 2 1 1 and thmB_arith_exists's conclusion;
CheapAchievable 2 2 (S(2^2)) and SignedAchievable 2 3 (S(2^2)); not CheapAchievable 2 2 3 (sharp); construction output
feeds targetD_of_momentTarget; infinite P exists for every N != 0 (Nat.infinite_setOfPred_prime_modEq_one).
Not covered: cyclotomic O; concrete twisted cores meeting the hypothesis; several cores per degree, degree 0; A1;
(B_p - delta)/p; B corollaries (degree p, mod 9); (H5), (H6), tables; (H9), (H10); fixed v; the R-053 index shift.
