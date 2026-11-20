# Seat M2b report: literature for M2 (20 Nov 2026)

Saved by the director from the seat's returned text (the harness refused the seat's own file write). Pages were read
through a fetch tool that returns a model-written digest; key comments were re-queried with targeted prompts.
[checked] marks formulas the seat verified itself.

## 0. Coverage
Read in full (digest): Research Threads III (all chunks), IV, V; draft-paper thread (29 Jun 2010); wiki pages Finding
primes, Prime counting function, Polynomial strategy; arXiv:1009.3956 v4 (pdf and ar5iv sections 2, 4); Lelechenko
arXiv:1305.1639 v3; Croot's f2_idea, fast_strassen, fast_primes, prime_generate; squarerootbarrier.pdf (local, raw).
Snippets or abstracts only: Thread II (first 100k of 324k chars, predates the parity idea); Hirsch, Kessler and
Mendlovic 2212.09857; Alboiu 2015 (zbMATH review); Chrobak and Craig 2608.18892; Semantic Scholar citing list (titles).
Unreachable: wiki Special:AllPages; web.archive.org. No separate wiki page on parity of pi; it is on Prime counting function.
Notation: Polymath's tau_2 counts ordered triples abc = n (our d_3); their tau_k(p) = k + 1.

## 1. Thread comments
Thread III: https://polymathprojects.org/2009/08/13/research-thread-iii-determinstic-way-to-find-primes/
- Croot 16 Aug #comment-556: parity of pi via sum of tau mod 4; proposes mod 3, 5, then CRT.
- Tao 16 Aug #558: hyperbola method; smooth to rough by convolution seems related to the parity problem.
- Croot 17 Aug #568: working mod small primes might escape parity objections.
- Tao 17 Aug #569: mod 3 needs tau_2, since one wants tau_2(p) = 3.
- Tao 17 Aug #570: D_3 only about x^(2/3); sum mod 9 encodes pi mod 3 modulo simpler terms.
- Tao 17 Aug #580: tau_k mod (k+1)^2 in x^(1/2+o(1)) gives pi mod (k+1); suspects k = 2 hardest.
- Lattice-point exchange 17 Aug: Croot #576, #584; Tao #588 (objection); Croot #589 (concedes).
- Kowalski #586 (Fouvry on tau_k). Lewko #594, #601, #605 (Linnik, D_k; Titchmarsh exponent conjecture iff Lindelof).
- Tao 18 Aug #615: naive abc <= x costs x^(2/3); FFT route hits carry problems. Lewko #628, #637.
- Croot 22 Aug #648: cubic character chi mod 7, tau* = chi * 1; on squarefree n, tau*(n^2) mod 9 picks out primes;
  blocked by term count. [checked] tau*(p^2) is 3 or 0, so it counts primes == +-1 mod 7, not pi(x) mod 3.
- Tao 22 Aug #652 to #654 (Meissel-Lehmer bottleneck x^(2/3)); Tao 24 Aug #670 (2 pi == sum tau mu^2 mod 4);
  Lewko #673 (squarefree count in x^(1/3)); Croot 24 Aug #679, #680 (hopes for pi mod 3 far below sqrt; caveat);
  McKenzie #703 (Linnik identity about n^(4/5)).
Thread IV: https://polymathprojects.org/2009/08/28/research-thread-iv-determinstic-way-to-find-primes/
- Tao's post 28 Aug: parity at x^(1/2+o(1)); for mod 3 the team cannot break x^(2/3+o(1)).
- Croot #710 (squarerootbarrier.pdf); Tao #715, #719, #722 (parity oracle, bisection, possible obstruction);
  Helfgott #723, #724 (sum tau in N^(1/3) log^3 N), #725 (only q | pi(x+t) - pi(x) needed); Tao #729 (30 Aug, 5/11);
  Lewko 31 Aug #734, #736, #737 (Voronoi error terms; D_3 method O(x^(2/3));
  http://lewko.wordpress.com/files/2009/08/voronoi.pdf); Kalai 3 Sep #755 (mod 4 easier than mod 3? unanswered);
  Tao #938, #971 (residue-class parity mod q via polynomial method).
- No comment explains why mod 3 fails beyond the cost of the D_3 sum.
Thread V: https://polymathprojects.org/2009/10/27/research-thread-v-determinstic-way-to-find-primes/
- Mod 2 only. Tao #1855, #1903 (obstructions); Lewko #1864, #1866; Croot #2015 (15 Jun 2010, prime_generate.pdf).
Draft paper thread: https://polymathprojects.org/2010/06/29/draft-version-of-polymath4-paper/
- W. D. Smith 23 Mar 2012 #5325: 2^(m omega) counts primes mod 2^m. No reply.
Paper (Math. Comp. 81 (2012); arXiv:1009.3956): section 2 (2.1) 2^omega = sum mu(d) tau(n/d^2); section 4 mod-3
identity mod 9 ([checked] equals 3k at p^k), N^(2/3-c), methods deteriorate rapidly in q. No obstruction statements.
Wiki: https://michaelnielsen.org/polymath1/index.php?title=Prime_counting_function (parity method, 5/11, mod 3
bottleneck #{abc < x} at x^(2/3)). Finding_primes and Polynomial_strategy: no mod 3 content.

## 2. Novelty
- O1: not found. Nearest: Tao #558; Croot #568 (opposite view); Chrobak and Craig 2608.18892 (different family,
  similar mod-p obstruction flavour; abstract only).
- O2: partly known as intuition (Tao #569); sufficiency in #580, paper section 4, Croot #648, Smith #5325
  (2^(m omega) is the trivial unsigned upper bound that the Kempner degree would improve). No necessity proof found.
- A19: the "if" direction (fast D_3 mod 9 gives fast pi mod 3) is essentially in Polymath4. Not found: the "only if"
  direction, the floor(x^(1/3)) + 3H identity, the Kempner degrees.
- Lelechenko v3: "9/23" not verbatim. Theorem 5 is the general deceleration formula; Theorem 2 (7/15 parity) depends
  on it via Example 13, so a gap in Theorem 5 would reach it. Gap not verified by this seat.
- Searched: MathOverflow, math.SE, arXiv (pi mod 3, parity of pi, parity barrier, z^omega mod p, 3^omega mod 9, tau_3
  algorithms, Lelechenko); 45 papers citing Polymath4 screened by title (incl. Alboiu, Ramanujan J. 2015; Sladkey;
  Helfgott and Thompson; Li 2609.29949, unreviewed). None states O1 or O2.

## 3. Croot's later notes (https://ecroot.math.gatech.edu/)
- f2_idea.pdf (3 Sep 2009, #754): Vandermonde-type argument for the F_2[x] approach; goals only.
- fast_strassen.pdf (14 Sep, #846): sum x^(d^2) mod (2, g) by Strassen.
- fast_primes.pdf (21 Sep, #881): prime generating function mod (2, g) on short intervals, z^(1/2 - Omega(c)).
- prime_generate.pdf (15 Jun 2010, Thread V #2015): N^(1/2 - eps) for primes mod 2; source of paper section 3.
None mentions mod 3; M2 does not need them (prime_generate only if the note cites the polynomial result).
Higher priority to acquire: 1009.3956 v4 (in hand), Sladkey 1206.3369, Lelechenko 1305.1639 v3, Lewko's voronoi.pdf.

## 4. pi(x) mod 3 below x^(1/2), unconditionally
Not found. Polymath4: N^(2/3-c). Sladkey's x^(5/9) D_3 with the Polymath reduction should give about x^(5/9) (seat's
inference; not stated anywhere). Exact pi: x^(1/2+o(1)) (Lagarias and Odlyzko 1987; Hirsch, Kessler and Mendlovic).
Unreviewed, existence noted only: ETH-refutation preprint (26 Oct 2026), Tulsyan 2611.00116, Li 2609.29949 (D_2 only).

## Bibliography
Threads and wiki as above. Thread II: https://polymathprojects.org/2009/08/09/research-thread-ii-deterministic-way-to-find-primes/
Paper: https://www.ams.org/mcom/2012-81-278/S0025-5718-2011-02542-1/ ; https://arxiv.org/abs/1009.3956
arXiv: 1305.1639, 1206.3369, 2212.09857, 2608.18892, 2101.08773. Alboiu: https://doi.org/10.1007/s11139-014-9596-1
