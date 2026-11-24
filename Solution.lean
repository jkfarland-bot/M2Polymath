module

public import Mathlib
public import ChallengeDefs
import all ChallengeDefs
public import Construct
public import A1
public import BCor
public import M2Ternary
public import M2BlockS
public import N2
public import CostAll

public section

/-!
# Proved solution

Each compared declaration below has exactly the statement of its counterpart in `Challenge.lean`.
The definitions are the same text as in `Challenge.lean`; the section "Bridges" shows each one
equal to the definition used in the development (`lean/`), and each theorem is then proved from the
development's theorem: `M2L.Zcheap_eq`, `M2L.Zsigned_eq` (Construct), `M2L2.not_targetU_untwisted`
(A1), `M2L2.not_targetD_below_p` and `M2L2.mod9_iff` (BCor), `M2L3.ternary_M1` (M2Ternary) and
`M2L5.piMod3_correct` (M2BlockS); Theorem 9.1 from `M2L4.Wfun_one`, `M2L4.Wfun_eight_dvd`
(M2TheoremL), `M2L6n.Wfun_prime_pow`, `M2L6n.L_summed_mod8_Wfun` and `M2L6n.L_N3_Wfun` (N2);
Theorem 7.20 (2), (3) from `M2L6c.blockStep_checks`, `M2L6c.blockStep_fast`, `M2L6c.blockStep_tail`,
`M2L6c.tail_short` and `M2L6c.blockSZ_nblocks` (CostAll).
-/

open Finset ArithmeticFunction
open scoped Nat ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

-- The development declares its own `Fact (Nat.Prime 3)` instance (BCor); switch it off so that the
-- definitions below elaborate exactly as in `Challenge.lean`, with Mathlib's `Nat.fact_prime_three`.
attribute [-instance] M2L2.fact_prime_three

namespace M2Polymath

/-! ## Bridges to the development -/

private theorem kempner_eq (p : ℕ) [Fact p.Prime] (k : ℕ) : kempner p k = FrobLevel.kempner p k := by
  have h := FrobLevel.exists_kempner p k
  unfold kempner FrobLevel.kempner
  apply le_antisymm
  · exact Nat.sInf_le (Nat.find_spec h)
  · exact Nat.find_min' h (Nat.sInf_mem h)

private theorem cheap_iff (p : ℕ) [Fact p.Prime] (k Z : ℕ) :
    CheapAchievable p k Z ↔ M2L.CheapAchievable p k Z := Iff.rfl

private theorem signed_iff (p : ℕ) [Fact p.Prime] (k Z : ℕ) :
    SignedAchievable p k Z ↔ M2L.SignedAchievable p k Z := Iff.rfl

private theorem targetU_iff (p : ℕ) [Fact p.Prime] {ι : Type*} (k : ℕ) (I : Finset ι) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) : TargetU p k (famI I c G h) ↔ M2L2.TargetU p k (M2L2.famI I c G h) :=
  Iff.rfl

private theorem targetD_famI_iff (p : ℕ) [Fact p.Prime] {ι : Type*} (I : Finset ι) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) :
    TargetD p 1 1 (famI I c G h) ↔ M2L.TargetD p 1 1 (M2L2.famI I c G h) := Iff.rfl

private theorem targetD_mod9_iff (a : ℤ → ℤ) :
    TargetD 3 1 1 (fam {1, 2, 3} a zpowZeta hcorr) ↔
      M2L.TargetD 3 1 1 (M2L.fam {1, 2, 3} a M2L.zpowZeta M2L.hcorr) := Iff.rfl

private theorem D3_eq (x : ℕ) : D3 x = M2L3.D3 x := rfl

private theorem icbrt_eq (x : ℕ) : icbrt x = M2L3.icbrt x := rfl

private theorem H_eq (x : ℕ) : H x = M2L3.H x := rfl

private theorem bfirstAux_eq (p : ℕ → Bool) :
    ∀ n lo hi, hi - lo ≤ n → bfirstAux p n lo hi = M2L5.bfirst p lo hi := by
  intro n
  induction n with
  | zero =>
    intro lo hi h
    rw [M2L5.bfirst]
    simp only [bfirstAux]
    split_ifs with h1 <;> first | rfl | omega
  | succ n ih =>
    intro lo hi h
    rw [M2L5.bfirst]
    simp only [bfirstAux]
    split_ifs with h1 h2
    · exact ih _ _ (by omega)
    · exact ih _ _ (by omega)
    · rfl

private theorem bfirst_eq : bfirst = M2L5.bfirst := by
  funext p lo hi
  exact bfirstAux_eq p (hi - lo) lo hi le_rfl

private theorem icbrtF_eq : icbrtF = M2L5.icbrtF := by
  funext n; unfold icbrtF M2L5.icbrtF; rw [bfirst_eq]

private theorem countLe_eq : countLe = M2L5.countLe := by
  funext P y k; unfold countLe M2L5.countLe; rw [bfirst_eq]

private theorem approxAux_eq : approxAux = M2L5.approxAux := by
  funext Q fuel
  induction fuel with
  | zero => funext u v p0 q0 p1 q1 best; rw [approxAux, M2L5.approxAux]
  | succ fuel ih => funext u v p0 q0 p1 q1 best; rw [approxAux, M2L5.approxAux, ih]

private theorem approx_eq : approx = M2L5.approx := by
  funext u v Q; unfold approx M2L5.approx; rw [approxAux_eq]

private theorem direct_eq : direct = M2L5.direct := rfl

private theorem cnt3_eq : cnt3 = M2L5.cnt3 := by
  funext y a q m f k; unfold cnt3 M2L5.cnt3; rw [countLe_eq]

private theorem corr_eq : corr = M2L5.corr := by
  funext y n0 a q s k ρ; unfold corr M2L5.corr; rw [cnt3_eq]

private theorem clsRho_eq : clsRho = M2L5.clsRho := rfl

private theorem blockFast_eq : blockFast = M2L5.blockFast := by
  funext y n0 a q ainv k; unfold blockFast M2L5.blockFast; rw [corr_eq, clsRho_eq]

private theorem blockStep_eq : blockStep = M2L5.blockStep := by
  funext y r n0; unfold blockStep M2L5.blockStep; rw [icbrtF_eq, approx_eq, direct_eq, blockFast_eq]

private theorem loop_eq : loop = M2L5.loop := by
  funext y r fuel
  induction fuel with
  | zero => funext n0; rw [loop, M2L5.loop, direct_eq]
  | succ fuel ih => funext n0; rw [loop, M2L5.loop, blockStep_eq, ih]

private theorem blockS_eq : blockS = M2L5.blockS := by
  funext y L; unfold blockS M2L5.blockS blockSZ M2L5.blockSZ; rw [icbrtF_eq, direct_eq, loop_eq]

private theorem D3fast_eq : D3fast = M2L5.D3fast := by
  funext x
  unfold D3fast M2L5.D3fast D3fastZ M2L5.D3fastZ BsumF M2L5.BsumF EabF M2L5.EabF EbcF M2L5.EbcF
  rw [icbrtF_eq, blockS_eq]

private theorem piMod3OfD3_eq : piMod3OfD3 = M2L4.piMod3OfD3 := rfl

private theorem piMod3_eq : piMod3 = M2L5.piMod3 := by
  funext x; unfold piMod3 M2L5.piMod3; rw [piMod3OfD3_eq, D3fast_eq]

private theorem nblocks_eq : nblocks = M2L6c.nblocks := by
  funext y r fuel
  induction fuel with
  | zero => funext n0; rw [nblocks, M2L6c.nblocks]
  | succ fuel ih => funext n0; rw [nblocks, M2L6c.nblocks, blockStep_eq, ih]

private theorem Wfun_eq : Wfun = M2L4.Wfun := rfl

private theorem R27_eq : R27 = M2L6n.R27 := rfl

private theorem piR_R27_eq (x : ℕ) : piR R27 x = M2L4.piR M2L6n.R27 x := rfl

private theorem CR_R27_eq (x : ℕ) : CR R27 x = M2L4.CR M2L6n.R27 x := rfl

/-! ## Results -/

/-- **Exact degree, cheap nodes.** For a prime `p` and `k ≥ 1`, the least `Z` such that the family
with cores `ζ^z`, `z ∈ {1, ..., Z}`, reaches target `D_k` is the Kempner value `S(p^k)`. -/
theorem exact_degree_cheap (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievable p k Z} (kempner p k) := by
  rw [kempner_eq]
  exact M2L.Zcheap_eq p hk

/-- **Exact degree, signed nodes.** For a prime `p` and `k ≥ 1`, the least `Z` such that the family
with cores `ζ^z` and `μ^|z|`, `z ∈ {-Z, ..., -1} ∪ {1, ..., Z}`, reaches target `D_k` is the
Kempner value `S(p^⌈k/2⌉)`. -/
theorem exact_degree_signed (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | SignedAchievable p k Z} (kempner p ((k + 1) / 2)) := by
  rw [kempner_eq]
  exact M2L.Zsigned_eq p hk

/-- **No prime detection (Corollary A1).** Let `k ≥ 1`. Take multiplicative cores `G_i` whose value
at every prime is the integer `deg i`, corrections `h_i` vanishing on squarefree `m > 1`, and any
integer coefficients. Then no member `∑ c_i (G_i * h_i)` is the prime indicator modulo `p^k`. -/
theorem no_prime_detection (p : ℕ) [Fact p.Prime] {ι : Type*} {k : ℕ} (hk : 1 ≤ k)
    (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative) (hGq : ∀ i ∈ I, ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) :
    ¬ TargetU p k (famI I c G h) :=
  M2L2.not_targetU_untwisted p hk I deg c G h hG hGq hh

/-- **Degree `p` is needed.** With degrees in `{0, ..., p - 1}`, cores congruent to their degree
modulo `p^2` at every prime of an infinite set `P`, and corrections divisible by `p^2` on squarefree
`m > 1`, no member of the family meets target `D_1` with offset `1`. -/
theorem degree_p_needed (p : ℕ) [Fact p.Prime] {ι : Type*} (I : Finset ι) (deg : ι → ℤ)
    (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite)
    (hPp : ∀ q ∈ P, q.Prime) (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ p - 1)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m) :
    ¬ TargetD p 1 1 (famI I c G h) :=
  M2L2.not_targetD_below_p p I deg c G h P hP hPp hd hG hGq hh

/-- **Modulo 9.** The member `a_1 B_1 + a_2 B_2 + a_3 B_3`, built as `fam {1, 2, 3} a zpowZeta hcorr`,
meets target `D_1` with offset `1` at `p = 3` if and only if `9 ∣ a_1`, `9 ∣ a_2` and `3 ∤ a_3`. -/
theorem mod9_iff (a : ℤ → ℤ) :
    TargetD 3 1 1 (fam {1, 2, 3} a zpowZeta hcorr) ↔
      (9 : ℤ) ∣ a 1 ∧ (9 : ℤ) ∣ a 2 ∧ ¬ (3 : ℤ) ∣ a 3 :=
  M2L2.mod9_iff a

/-- **The ternary identity (M1).** For every natural `x`, `D_3(x) = ⌊x^(1/3)⌋ + 3 H(x)`. -/
theorem d3_ternary (x : ℕ) : D3 x = icbrt x + 3 * H x :=
  M2L3.ternary_M1 x

/-- **`π(x) mod 3` is computed correctly.** For every natural `x`, `piMod3 x = π(x) mod 3`. -/
theorem piMod3_correct (x : ℕ) : piMod3 x = (Nat.primeCounting x : ZMod 3) := by
  rw [piMod3_eq]
  exact M2L5.piMod3_correct x

/-- **Theorem 9.1 (1) of the preprint** (https://doi.org/10.5281/zenodo.24485458), equation (N1),
pointwise: `W(1) = 1`, and `8 ∣ W(n)` whenever `ω(n) ≥ 2`. -/
theorem normCount_one_and_eight_dvd :
    Wfun 1 = 1 ∧ ∀ n : ℕ, 2 ≤ ω n → (8 : ℤ) ∣ Wfun n := by
  rw [Wfun_eq]
  exact ⟨M2L4.Wfun_one, fun _ h => M2L4.Wfun_eight_dvd h⟩

/-- **Theorem 9.1 (2) of the preprint** (https://doi.org/10.5281/zenodo.24485458), (N2): the values
of `W` at prime powers. For a prime `q` and `j ≥ 1`, `W(q^j) = 4` if `q > 3`, `q ≡ 1 (mod 3)` and
(`q = a^2 + 27 b^2` or `3 ∣ j`), and `W(q^j) = 0` otherwise. -/
theorem normCount_prime_pow (q j : ℕ) (hq : q.Prime) (hj : 1 ≤ j) :
    Wfun (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ (R27 q ∨ 3 ∣ j) then 4 else 0 :=
  M2L6n.Wfun_prime_pow q j hq hj

/-- **Theorem 9.1 (3) of the preprint** (https://doi.org/10.5281/zenodo.24485458), the summed
formula modulo 8: for `x ≥ 1`, `∑_{n ≤ x} W(n) ≡ 1 + 4 (π_R(x) + C_R(x)) (mod 8)` with `R` the
primes of the form `a^2 + 27 b^2`. -/
theorem normCount_mod8 {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, Wfun n ≡ 1 + 4 * ((piR R27 x : ℤ) + CR R27 x) [ZMOD 8] := by
  rw [piR_R27_eq, CR_R27_eq, Wfun_eq]
  exact M2L6n.L_summed_mod8_Wfun hx

/-- **Theorem 9.1 (3) of the preprint** (https://doi.org/10.5281/zenodo.24485458), (N3): for
`x ≥ 1`, `4 ∣ ∑_{n ≤ x} W(n) - 1`, and the number of primes `q ≤ x` of the form `a^2 + 27 b^2` is
congruent modulo 2 to `(∑_{n ≤ x} W(n) - 1) / 4 - C_R(x)`. -/
theorem normCount_parity {x : ℕ} (hx : 1 ≤ x) :
    (4 : ℤ) ∣ ∑ n ∈ Ioc 0 x, Wfun n - 1 ∧
      (piR R27 x : ℤ) ≡ (∑ n ∈ Ioc 0 x, Wfun n - 1) / 4 - CR R27 x [ZMOD 2] := by
  rw [piR_R27_eq, CR_R27_eq, Wfun_eq]
  exact M2L6n.L_N3_Wfun hx

/-- **Theorem 7.20 (2) of the preprint** (https://doi.org/10.5281/zenodo.24485458), the fast path.
Under the routine's setup `1 ≤ y`, `y < n0 ^ 3` (that is `n0 > ⌊y^(1/3)⌋`), with
`Q = icbrtF (n0 ^ 3 / y)` and `(a, q) = approx y (n0 * n0) Q`: `1 ≤ Q`, `1 ≤ q ≤ Q`, and whenever
`q ≤ R = r + 1 - n0` the run-time checks of `blockStep` pass, so that it returns the block of length
`k q` with `k = min Q R / q` and the fast sum `blockFast y n0 a q (gcdA a q) k`. -/
theorem blockStep_fast_path (y r n0 : ℕ) (hy : 1 ≤ y) (hn : y < n0 ^ 3) :
    let Q := icbrtF (n0 ^ 3 / y)
    let a := (approx y (n0 * n0) Q).1
    let q := (approx y (n0 * n0) Q).2
    let R := r + 1 - n0
    1 ≤ Q ∧ 1 ≤ q ∧ q ≤ Q ∧
      (q ≤ R →
        (|(q : ℤ) * y - (a : ℤ) * (n0 : ℤ) ^ 2| * (((min Q R / q * q : ℕ) : ℤ) - 1) < (n0 : ℤ) ^ 2 ∧
          (q : ℤ) * y * (((min Q R / q * q : ℕ) : ℤ) - 1) ^ 2 ≤ (n0 : ℤ) ^ 3 ∧
          ((a : ℤ) * Nat.gcdA a q) % (q : ℤ) = 1 % (q : ℤ)) ∧
        blockStep y r n0 = (min Q R / q * q, blockFast y n0 a q (Nat.gcdA a q) (min Q R / q))) := by
  have h1 := M2L6c.blockStep_checks y r n0 hy hn
  have h2 := M2L6c.blockStep_fast y r n0 hy hn
  simp only [icbrtF_eq, approx_eq, blockStep_eq, blockFast_eq]
  dsimp only at h1
  exact ⟨h1.1, h1.2.1, h1.2.2.1, fun h => ⟨h1.2.2.2 h, h2 h⟩⟩

/-- **Theorem 7.20 (2) of the preprint** (https://doi.org/10.5281/zenodo.24485458), the tail. Under
the routine's setup `1 ≤ y`, `y < n0 ^ 3` and `n0 ≤ ⌊√y⌋`, if `R = r + 1 - n0 < q` (with `Q` and `q`
as in `blockStep_fast_path`) then `blockStep` sums the rest of the range directly, and that direct
sum is short: `R < Q` and `Q ^ 6 ≤ y`. -/
theorem blockStep_tail_short (y r n0 : ℕ) (hy : 1 ≤ y) (hn : y < n0 ^ 3) (hr : n0 ≤ Nat.sqrt y)
    (hR : r + 1 - n0 < (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2) :
    blockStep y r n0 = (r + 1 - n0, direct y n0 (r + 1 - n0)) ∧
      r + 1 - n0 < icbrtF (n0 ^ 3 / y) ∧ icbrtF (n0 ^ 3 / y) ^ 6 ≤ y := by
  rw [icbrtF_eq, approx_eq] at hR
  rw [icbrtF_eq, blockStep_eq, direct_eq]
  have h1 := M2L6c.blockStep_checks y r n0 hy hn
  dsimp only at h1
  exact ⟨M2L6c.blockStep_tail y r n0 hR, by omega, M2L6c.tail_short hy hr⟩

/-- **Theorem 7.20 (3) of the preprint** (https://doi.org/10.5281/zenodo.24485458), the number of
blocks. For every `y ≥ 1` and every `L`, the loop `loop y r (r + 1) n1` of `blockSZ y L`
(`r = ⌊√y⌋`, `n1 = max (L + 1) (min (icbrtF y + 1) (r + 1))`) makes at most
`4 (⌊y^(1/3)⌋ + 1) (⌊log₂ y⌋ + 2) + 1` calls of `blockStep`. -/
theorem block_count (y L : ℕ) (hy : 1 ≤ y) :
    nblocks y (Nat.sqrt y) (Nat.sqrt y + 1) (max (L + 1) (min (icbrtF y + 1) (Nat.sqrt y + 1)))
      ≤ 4 * (icbrt y + 1) * (Nat.log 2 y + 2) + 1 := by
  rw [nblocks_eq, icbrtF_eq, icbrt_eq]
  exact M2L6c.blockSZ_nblocks y L hy

end M2Polymath
