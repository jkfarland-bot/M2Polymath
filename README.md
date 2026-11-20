# M2Polymath: pi(x) mod 3, divisor sums and the exact degree

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24408424.svg)](https://doi.org/10.5281/zenodo.24408424)

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
| `lean/AllAxioms.lean` | Scans every declaration and reports any axiom beyond propext, Classical.choice, Quot.sound |
| `PROOF_D3_5_9.md` | The full proof that D_3(x) is computable in O(x^(5/9) log^2 x) operations |
| `code/` | Exact-arithmetic check scripts (Python 3, run with `python3 -I`) with their recorded outputs, one folder per review seat |
| `reviews/` | The review reports: worker, verifier and cold-reader verdicts, and the statement audits of each Lean round |
| `ledger/` | The ledger entries recording each verified result |

Paths of the form `m2/<seat>/` in the reviews and ledger correspond to `code/<seat>/` here.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.33.1) and Mathlib (rev 0df444a3) are pinned.

```bash
lake exe cache get   # download prebuilt Mathlib
lake build           # builds every module, the audit files and AllAxioms
```

`lake build` prints the axiom report; the expected final line is
`declarations scanned: N; nonstandard axiom uses: 0`. No file uses `sorry`, `admit`, `native_decide`, `axiom`
or `implemented_by`. Bounded checks (table rows, witness primes) use kernel `decide`.

## How the work was checked

Each result passed at least two independent reviewers who had not seen the source's own verdicts: a worker who
checked the proof and wrote code from the definitions, then a verifier or cold reader. Each Lean round was rebuilt
from scratch, scanned for axioms, tested with a deliberately planted error per file (each must fail), and audited by
a separate reader for whether the Lean statements mean what the mathematics claims and whether any hypothesis is
vacuous. "No prior art found" in the reviews is never a claim of novelty.

## Prior art

Polymath4, D. H. J. Polymath, "Deterministic methods to find primes", Math. Comp. 81 (2012),
[arXiv:1009.3956](https://arxiv.org/abs/1009.3956); E. Croot, note of 28 Aug 2009 (parity of pi(x) in x^(5/11));
R. Sladkey, [arXiv:1206.3369](https://arxiv.org/abs/1206.3369); A. Lelechenko,
[arXiv:1305.1639](https://arxiv.org/abs/1305.1639); J. C. Lagarias and A. M. Odlyzko (1987); D. Hirsch, I. Kessler and
U. Mendlovic, [arXiv:2212.09857](https://arxiv.org/abs/2212.09857).

## Citation

Version 1.0.0: [10.5281/zenodo.24408424](https://doi.org/10.5281/zenodo.24408424). All versions: [10.5281/zenodo.24408423](https://doi.org/10.5281/zenodo.24408423).

## License

Apache License 2.0 (see `LICENSE`).
