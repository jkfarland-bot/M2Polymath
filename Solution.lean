module

public import Mathlib
public import ChallengeDefs
import all ChallengeDefs
public import Construct
public import A1
public import BCor
public import M2Ternary
public import M2BlockS

public section

/-!
# Proved solution

Each compared declaration below has exactly the statement of its counterpart in `Challenge.lean`.
The definitions are the same text as in `Challenge.lean`; the section "Bridges" shows each one
equal to the definition used in the development (`lean/`), and each theorem is then proved from the
development's theorem: `M2L.Zcheap_eq`, `M2L.Zsigned_eq` (Construct), `M2L2.not_targetU_untwisted`
(A1), `M2L2.not_targetD_below_p` and `M2L2.mod9_iff` (BCor), `M2L3.ternary_M1` (M2Ternary) and
`M2L5.piMod3_correct` (M2BlockS).
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

end M2Polymath
