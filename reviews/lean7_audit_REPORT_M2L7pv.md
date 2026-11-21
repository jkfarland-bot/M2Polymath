# Seat M2L7p-v report: audit of the version 1.3.0 Palomar statements (21 Nov 2026)

Saved by the director from the seat's returned text (condensed; the seat wrote none of the files and saw no verdict).

VERDICT: FAITHFUL WITH CAVEATS (both minor; caveat 1 fixed by the director before release).

Fidelity. The new definitions match preprint version 2.0 (10.5281/zenodo.24423389): rStar counts primitive pairs with
signs (the box |a|, |b| <= n holds every solution; n = 0 gives 0); Wfun = 2^omega r*/2 for gcd(n, 6) = 1, else 0, with
exact division; R27, piR, piPlus and CR as in the preprint (CR sums j from 2 to Nat.log 2 x, iroot is floor(x^(1/j)));
nblocks has the recursion and fuel shape of loop. block_count bounds the loop actually run by blockSZ (same start and
fuel). The four Theorem 9.1 statements say what the preprint says (parenthesization of the parity formula checked).
Theorem 7.20 (2) and (3) are as strong as the preprint or stronger (r free; no n0 <= r hypothesis on the fast path).

Caveats.
1. blockStep_fast_path stated the returned value but not the three run-time checks themselves. FIXED in the release:
   the three check inequalities are now conjuncts, proved from M2L6c.blockStep_checks; a planted change to one of them
   is rejected by the comparator ("theorem statement do not match").
2. blockStep_tail_short puts n0 <= floor(sqrt y) on the whole conclusion; the preprint needs it only for Q^6 <= y.
   Cosmetic (the statement is slightly weaker in a hypothesis that the routine's setup always satisfies).

Unchanged originals: Challenge.lean is purely additive against v1.2.0 (docstring, new definitions, seven theorems);
the seven earlier statements and all earlier definitions are byte-identical; comparator.json only gains the seven
names; lean/ChallengeDefs.lean mirrors the new definitions (and loses one stray blank line).

Checks: lake build Challenge Solution succeeds; check-challenge-defs.py and check-lean-sources.py pass; the sandboxed
comparator accepts with con-ron, nanoda and the Lean kernel.

Non-vacuity: a computable copy of Wfun (proved equal) gives W(1) = 1, W(31) = 4, W(7) = 0, W(25) = 0, W(343) = 4,
W(31*43) = 16, W(91) = 8. nblocks at y = 1000, 10^6, 99999999 is 15, 298, 1830 against bounds 485, 8485, 52081.
The fast-path hypotheses are kernel-checked at y = 1000, n0 = 11; a nontrivial block at y = 10^6, n0 = 305 (Q = q = 3).
The tail hypotheses are satisfiable (kernel-checked at y = 1000, n0 = 11, r = 10).

Planted tests (on copies, restored byte-identical): Wfun with /4: rejected (Const does not match M2Polymath.Wfun);
block_count bound 3* instead of 4*: rejected (theorem statement do not match); nblocks without 1 +: rejected
(Const does not match M2Polymath.nblocks._f).
