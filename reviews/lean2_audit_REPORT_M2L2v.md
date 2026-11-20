# Seat M2L2-v: statement audit of m2/lean2 (20 Nov 2026)
Saved by the director from the seat's returned text. Audit file m2/lean2_audit/AuditV2.lean (EXIT 0; one unused-variable lint).
Director rebuild: m2/lean2_dir_rebuild (8 files exit 0, no warnings; 322 declarations, only propext, Classical.choice,
Quot.sound). Worker: 50 main theorems' #print axioms standard; 8 of 8 planted errors fail.
Verdicts: FamGen FAITHFUL (iff cores: any multiplicative G with G(q) = deg i, broader than the paper's cheap set, so the
lower bound is stronger; construction uses pure zeta powers; IsLeast transfers). A1 FAITHFUL WITH CAVEATS (TargetU fixes
prime value 1 mod p^k; weakest form is corA1_I_false / corA1_O; prime indicator mod p^k excluded for k >= 1;
Bp_sub_delta faithful and not an integral member). BCor FAITHFUL (mod9_I exactly the extract; mod9_iff sufficiency for
explicit members a_1 B_1 + a_2 B_2 + a_3 B_3; Vandermonde matches R-113). Twist FAITHFUL WITH CAVEATS (Z-valued
characters; signed_twisted_lower uses factor count, the |sdeg| form proved in the audit as signed_twisted_lower_sdeg).
Summatory FAITHFUL WITH CAVEATS (card_primePow_eq for every x incl. 0; H9_H10 exactly (H9), (H10) incl. ranges and sum a_z = F(1);
weights existential, not (H5); C = p^v u not necessarily positive). MuShift FAITHFUL (r = 0..L+1 suffices;
Q(-1) = (-1)^(L+1) (L+1)!; second proof of r25's count genuine, upper bound from hasLevel_kempner, no circularity).
RingO/TwistO FAITHFUL WITH CAVEATS (IntDvdDescends is the O cap Q = Z fix; proved for every ring of integers;
thmH_cyclotomic on CyclotomicField N Q; UnitModP correct; localized rings not instantiated).
Non-vacuity: twisted-list member meets TargetD 2 1 1 (trivial twist); member over O_{Q(zeta_4)} meets TargetDO 2 1 1;
mod9_iff satisfied by (0,0,1), fails for (3,0,1); H9_H10 on T = {1,2}, p = 2, k = 1; hasLevel_zeta_kempner hypothesis
met by r25; primePowLe 10 has 7 elements.
Not covered: (H5) explicit weights and tables; (H6) as a series; fixed v; integers prime to p inverted in O;
constructions/iff over O and with twisted cores; a TargetD member with a nontrivial character; Theorem B's finite-domain
remark; f^(*p) = E_p(Frob o f); converse of the mu shift; paper's cheap measure as a separate theorem (subsumed).
