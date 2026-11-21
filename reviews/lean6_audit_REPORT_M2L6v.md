# Seat M2L6-v report: audit of lean/CostAll.lean and lean/N2.lean (21 Nov 2026)

Saved by the director from the seat's returned text (condensed; the seat wrote neither file and saw no verdict).

VERDICT: FAITHFUL WITH CAVEATS.

(a) Rebuild: both files check with exit 0 (CostAll 16 s, N2 28 s). No sorry, native_decide, axiom, admit,
implemented_by, extern, unsafe or opaque. #print axioms: propext, Classical.choice, Quot.sound only.

(b) Fidelity, cost file. Every W-copy compared line by line with M2BlockS: bfirstW 1 per predicate evaluation;
icbrtW counts bisection evaluations; approxAuxW and xgcdAuxW count every Euclid step (6 each); countLeW charges each
search step and 8 per evaluation of P; `direct` is charged 1 per term everywhere it occurs; loopW 2 per call. No loop
or recursion is hidden in a constant; constants cover only O(1) work. Every _fst theorem is a real equality with the
original; blockSZW_fst ties the headline count to blockSZ. The check-failure branch is proved unreachable. nblocks uses
exactly loop's recursion. Hypotheses are the routine's real setup and are discharged by the loop proofs.
Fidelity, N2. Wfun_prime_pow is the hypothesis hWpp of M2TheoremL word for word with R := R27; the three
unconditional theorems pass Wfun_one, Wfun_eight_dvd and Wfun_prime_pow to L_summed_exact, L_summed_mod8, L_N3.

Caveats to state when citing:
1. The cost is a counter defined in the file under a unit-cost model on O(log y)-bit integers. Lean checks the bound;
   that the charges match real work was checked by reading (an undercharged copy would still check).
2. Nat.sqrt is charged 2 log2 y + 2 by assumption (library primitive, not instrumented); multiplications of
   multi-word numbers count as unit cost.
3. The bound is 2000 (icbrt y + 1)(log2 y + 2)^2 for y >= 1, uniform in L; measured counts are 100 to 1500 times below.
4. (Addressed in v1.2.0: the declarations were private in the audited copy and are public in the release.)
5. N2 uses a classical DecidablePred instance for R27 (affects computability of piR R27 only).

(c) Planted errors: 2000 to 20 in blockSZW_cost FAILS; 2000 to 1300 FAILS (proof needs about 1330); countLe charge
changes FAIL where the bound is tight and CHECK where there is slack (by design); left-search predicate change FAILS
(countLeW_fst); tail charge R to R*R FAILS; failure-branch charge inflated CHECKS (branch unreachable); tail charge
removed CHECKS (caveat 1); approx steps charged quadratically FAILS; 4 to 8 in Wfun_prime_pow FAILS; 27 to 26 in R27
FAILS; 3 | j to 2 | j FAILS.

(d) Non-vacuity: blockSZW y 0 at y = 1 to 10^7 gives costs 11 to 180,617 against bounds 16,000 to 2.7e8, values equal
to the brute-force sums (also for y = 10^6 with L = 7, 500, 999); nblocks at 10^7 is 747 (bound 21,601). A computable
copy of Wfun gives 4 at 31, 43, 127, 157, 343, 961 and 0 at 2, 4, 5, 7, 11, 13, 19, 25, 49, 1331, as (N2) predicts.

Director: both files rebuilt independently; planted error 4 to 8 in Wfun_prime_pow rejected. In v1.2.0 the files are
modules with public declarations; lake build scans 2,353 declarations with no nonstandard axiom, and the Palomar
comparator still accepts.
