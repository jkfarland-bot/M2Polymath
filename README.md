# M2Polymath: pi(x) mod 3, divisor sums and the exact degree

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24408423.svg)](https://doi.org/10.5281/zenodo.24408423)

**Author:** Joseph S. Farland

**AI assistance:** this work was prepared with Claude (Anthropic), an AI model, which helped draft the text, develop
and check the proofs, run the computations, and search the literature. Several results, marked "A19" in
[CLAIMS.md](CLAIMS.md), were first proposed by ChatGPT (OpenAI) in answer to a question from this project; each was
then independently checked here, and the checks and Lean proofs are by Claude. The formalized statements are
machine-checked in Lean 4; the rest is not. The author, Joseph S. Farland, chose the problems, directed the work, and
is responsible for its content. No external human referee has reviewed this work.

## What is here

In 2009 the Polymath4 project ("Deterministic methods to find primes") computed the parity of pi(x) below the
square-root barrier but stalled at x^(2/3) for pi(x) mod 3. This repository explains the stall and measures it,
for identities built from shifted and twisted zeta and Dirichlet L factors with squarefull corrections:

- **Obstruction.** On squarefree integers whose primes lie in a suitable residue class, every such identity collapses
  modulo p^m to a polynomial in z^omega(n). So no identity detects primes modulo p, and any identity giving the
  divided count needs a factor whose degree is divisible by p exactly once. For p = 3 a three-fold divisor sum
  cannot be avoided.
- **Exact degree.** The least degree that yields pi(x) mod p^k is S(p^ceil(k/2)) with inverse factors and S(p^k)
  without, where S is the Kempner function. Both are attained by explicit constructions.
- **Algorithms.** pi(x) mod 3 below the square root is equivalent to D_3(x) mod 9 below the square root, via
  D_3(x) = floor(x^(1/3)) + 3H(x). We prove D_3(x) is computable in O(x^(5/9) log^2 x) operations
  ([PROOF_D3_5_9.md](PROOF_D3_5_9.md)), closing a gap in the published x^(5/9) claim, so pi(x) mod 3 is computable in
  x^(5/9+o(1)) unconditionally. A Lean function computing pi(x) mod 3 this way is proved correct for every x.
- **A gap in the literature.** The 9/23 exponent from Lelechenko's Theorem 5 (arXiv:1305.1639) rests on an invalid
  step; the safe bound is 3/5 (5/9 with the faster D_3). His Example 14 is affected too; his Theorem 2 stands.
- **Exits that close.** S3 cubic fields, class-number-3 theta filters, and pointwise detection of primes
  a^2 + 27b^2 all fail inside the class.

[CLAIMS.md](CLAIMS.md) lists every result with its source, its review status and the Lean theorems that certify it.
Results that depend on unreviewed external work (an x^(1/3+o(1)) algorithm and a 47/104 parity exponent) are
recorded there as conditional and are not claimed.

## Layout

| Path | Contents |
|---|---|
| `lean/` | Lean 4 sources: the M2 development (five rounds) and the six library modules it builds on (Found, Upper, Lower, LowerPadic, DirBase, DirMain, from the author's Frobenius levels work) |
| `lean/Audit/` | Lemmas written by the independent statement auditors (for example `thetaJ_half`, `DType3_iff_d3`, `F9_in_relaxed`) |
| `lean/CostAll.lean` | Version 1.2.0: the operation count of the block routine for D_3 (fast path always taken, number of blocks, an instrumented copy proved equal to the routine with cost at most 2000 (icbrt y + 1)(log2 y + 2)^2, uniformly in the lower limit) |
| `lean/N2.lean` | Version 1.2.0: (N2) of Theorem L, so Theorem L is proved in Lean unconditionally |
| `lean/AllAxioms.lean` | Scans every declaration and reports any axiom beyond propext, Classical.choice, Quot.sound |
| `PROOF_D3_5_9.md` | The full proof that D_3(x) is computable in O(x^(5/9) log^2 x) operations |
| `code/` | Exact-arithmetic check scripts (Python 3, run with `python3 -I`) with their recorded outputs, one folder per review seat |
| `reviews/` | The review reports: worker, verifier and cold-reader verdicts, and the statement audits of each Lean round |
| `ledger/` | The ledger entries recording each verified result |

Paths of the form `m2/<seat>/` in the reviews and ledger correspond to `code/<seat>/` here.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0-rc2) and Mathlib (v4.35.0-rc2) are pinned.

```bash
lake exe cache get   # download prebuilt Mathlib
lake build           # builds every module, the audit files and AllAxioms
```

`lake build` prints the axiom report; the expected final line is
`declarations scanned: N; nonstandard axiom uses: 0`. No file uses `sorry`, `admit`, `native_decide`, `axiom`
or `implemented_by`. Bounded checks (table rows, witness primes) use kernel `decide`.

## Palomar layout (version 1.1.0; extended in 1.3.0)

Version 1.1.0 ports the development to Lean and Mathlib v4.35.0-rc2 and Lean's module system, with no change to any theorem statement, and adds the layout of the [Palomar registry](https://palomar-registry.org/):

| File | Contents |
|---|---|
| `Challenge.lean` | The statement surface a reader audits: every definition restated over Mathlib alone, and fourteen theorems with `sorry` (seven since 1.1.0, seven more since 1.3.0) |
| `Solution.lean` | Proves the same fourteen declarations from the development |
| `lean/ChallengeDefs.lean` | A copy of the definition block of `Challenge.lean`, which `Solution.lean` imports |
| `comparator.json` | The fourteen compared theorems and the permitted axioms (propext, Quot.sound, Classical.choice); no definition is left as a hole |
| `formalization.yaml` | Authorship, sources, AI assistance, scope and fidelity |
| `scripts/` | Palomar's checks, from the Palomar starter template |

The comparator checks every definition of `Challenge.lean` in full, body included, against the one `Solution.lean` exports, so no definition can be swapped for a weaker one. `Solution.lean` gets its definitions from `lean/ChallengeDefs.lean`, a copy of the same block, and `scripts/check-challenge-defs.py` checks that the two blocks are identical. A changed definition body in `Challenge.lean` was tested and is rejected.

The first seven compared theorems: `exact_degree_cheap` and `exact_degree_signed` (the exact degree, S(p^k) and S(p^ceil(k/2))), `no_prime_detection`, `degree_p_needed`, `mod9_iff`, `d3_ternary` (D_3(x) = floor(x^(1/3)) + 3H(x)) and `piMod3_correct` (a computable pi(x) mod 3, correct for every x). Since version 1.3.0 also `blockStep_fast_path`, `blockStep_tail_short` and `block_count` (Theorem 7.20 (2) and (3) of preprint version 2.0: the block routine's run-time checks always pass, and the number of blocks is O(y^(1/3) log y)), and `normCount_one_and_eight_dvd`, `normCount_prime_pow`, `normCount_mod8` and `normCount_parity` (Theorem 9.1: the parity of the number of primes a^2 + 27 b^2 from a weighted norm count). The operation counter of Theorem 7.20 (4) stays in `lean/CostAll.lean` and is not compared.

Checks, as Palomar runs them:

```bash
python3 scripts/check-lean-sources.py
python3 scripts/check-challenge-defs.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # needs bubblewrap (bwrap); expected: "Your solution is okay!"
```

## How the work was checked

Each result passed at least two independent reviewers who had not seen the source's own verdicts: a worker who
checked the proof and wrote code from the definitions, then a verifier or cold reader. Each Lean round was rebuilt
from scratch, scanned for axioms, tested with a deliberately planted error per file (each must fail), and audited by
a separate reader for whether the Lean statements mean what the mathematics claims and whether any hypothesis is
vacuous. "No prior art found" in the reviews is never a claim of novelty.

## Version 1.3.0

Extends the Palomar statement file with seven theorems from version 2.0 of the preprint ([10.5281/zenodo.24423389](https://doi.org/10.5281/zenodo.24423389)): Theorem 7.20 (2) and (3) (`blockStep_fast_path`, `blockStep_tail_short`, `block_count`) and Theorem 9.1 (`normCount_one_and_eight_dvd`, `normCount_prime_pow`, `normCount_mod8`, `normCount_parity`). New definitions in `Challenge.lean` (and its copy `lean/ChallengeDefs.lean`): `nblocks`, `rStar`, `Wfun`, `R27`, `piR`, `piPlus`, `CR`. The seven earlier statements and all earlier definitions are unchanged. The comparator compares every definition body and accepts with the Lean kernel, nanoda and con-ron. Written by Claude seat M2L7p and audited by a separate seat. Metadata now cites preprint version 2.0 and the Frobenius preprint ([10.5281/zenodo.24411195](https://doi.org/10.5281/zenodo.24411195)).

## Version 1.2.0

Adds two Lean files, written by Claude seats M2L6c and M2L6n and audited by a separate seat (twelve planted errors, line-by-line comparison of the instrumented functions with the originals):

- `lean/CostAll.lean` (namespace `M2L6c`): `approx` returns a continued-fraction convergent with 1 <= q <= Q (`approx_good`); the run-time checks of a block step always pass, so the fast branch is always taken (`blockStep_checks`, `blockStep_fast`); the block loop makes at most 4 (icbrt y + 1)(log2 y + 2) + 1 steps (`nblocks_le`); and an instrumented copy `blockSZW`, proved equal to the routine (`blockSZW_fst`), has cost at most 2000 (icbrt y + 1)(log2 y + 2)^2 for every lower limit (`blockSZW_cost`). The counter is defined in the file: one unit per term of a direct sum, per bisection probe, 8 per evaluation of a level polynomial, 6 per Euclid step; `Nat.sqrt` is charged 2 log2 y + 2 without instrumentation; operations on O(log y)-bit integers count as one unit. Lean checks the bound on this counter; that the charges match real work was checked by reading.
- `lean/N2.lean` (namespace `M2L6n`): (N2), the values of W at prime powers (`Wfun_prime_pow`), by an elementary argument (uniqueness of primitive representations, Thue's lemma, powers of x + y sqrt(-3)), and Theorem L unconditionally (`L_summed_exact_Wfun`, `L_summed_mod8_Wfun`, `L_N3_Wfun`).

The axiom report now scans 2,353 declarations, with no axiom beyond propext, Classical.choice and Quot.sound. The Palomar files (`Challenge.lean`, `Solution.lean`, `comparator.json`) are unchanged and the comparator still accepts.

## Prior art

Polymath4, D. H. J. Polymath, "Deterministic methods to find primes", Math. Comp. 81 (2012),
[arXiv:1009.3956](https://arxiv.org/abs/1009.3956); E. Croot, note of 28 Aug 2009 (parity of pi(x) in x^(5/11));
R. Sladkey, [arXiv:1206.3369](https://arxiv.org/abs/1206.3369); A. Lelechenko,
[arXiv:1305.1639](https://arxiv.org/abs/1305.1639); J. C. Lagarias and A. M. Odlyzko (1987); D. Hirsch, I. Kessler and
U. Mendlovic, [arXiv:2212.09857](https://arxiv.org/abs/2212.09857).

## Citation

Preprint: J. S. Farland, *The exact degree of divisor-sum identities for the prime-counting function modulo prime powers*, Zenodo, 2026, version 2.0 [10.5281/zenodo.24423389](https://doi.org/10.5281/zenodo.24423389), version 1 [10.5281/zenodo.24408923](https://doi.org/10.5281/zenodo.24408923) (all versions [10.5281/zenodo.24408922](https://doi.org/10.5281/zenodo.24408922)). Every theorem of the preprint is proved in this repository.

Software: version 1.0.0 [10.5281/zenodo.24408424](https://doi.org/10.5281/zenodo.24408424); version 1.1.0 [10.5281/zenodo.24411133](https://doi.org/10.5281/zenodo.24411133); version 1.2.0 [10.5281/zenodo.24421664](https://doi.org/10.5281/zenodo.24421664); version 1.3.0 [10.5281/zenodo.24424730](https://doi.org/10.5281/zenodo.24424730). All versions: [10.5281/zenodo.24408423](https://doi.org/10.5281/zenodo.24408423).

Palomar registry: version 1.1.0 (commit `0a2ef3f72382b44cd15953d64b86bc374af17852`) was accepted as entry PALOMAR-2026-11-21-000012, version 1; version 1.3.0 (commit `47f63036342b3cfc956a7f92d1d47c160cf3f8d4`, fourteen compared theorems) was accepted as version 2 of that entry.

## License

Apache License 2.0 (see `LICENSE`).
