/-
Run r25 / M2, seat M2L: the construction half of Theorem H, pointwise on all positive integers,
and the exact minimal node bounds for arithmetic functions.

Contents.
1. `Bz z`: `n -> z ^ omega(n)` (value `0` at `0`), multiplicative.
2. `zinv z`: the Dirichlet inverse of the core `zpowZeta z` (`moebius ^ z` for `z >= 0`,
   `zeta ^ |z|` for `z < 0`), and the correction `hcorr z = zinv z * Bz z`. Integral by
   construction; `zpowZeta z * hcorr z = Bz z`; `hcorr z` vanishes at every `n` having a prime
   that divides it exactly once (squarefull support), in particular on squarefree `n > 1`.
3. `construction_explicit`: for a nonempty node set `T` without `0` with `p^k | prod T`, weights
   `a` and `C = p^v u` (`p` not dividing `u`) such that `F = fam T a zpowZeta hcorr` has
   `F n = sum over z of a_z z^omega(n)` for every `n >= 1`, `F(q^e) = C` at every prime power,
   and `C p^k | F n` whenever `omega(n) >= 2`.
4. `cheap_arith_iff`, `signed_arith_iff`: the family (cores `zeta ^ z`, resp. `zeta ^ z` and
   `moebius ^ |z|`, integral corrections vanishing on squarefree `m > 1`) meets `TargetD p v k`
   for some `v` with nodes in `{1..Z}` iff `S(p^k) <= Z`; with nodes in
   `{-Z..-1} union {1..Z}` iff `S(p^ceil(k/2)) <= Z`. `IsLeast` forms:
   `Z_cheap(p, k) = S(p^k)`, `Z_signed(p, k) = S(p^ceil(k/2))`.

Lean v4.33.1 with Mathlib; imports DirBase, DirMain (r25 library), Moment, MomentZ, Slice.
No sorry.
-/
import Mathlib
import Found
import DirBase
import DirMain
import Moment
import MomentZ
import Slice

namespace M2L

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-! ## 1. `B_z(n) = z ^ omega(n)` -/

/-- `B_z(n) = z ^ omega(n)` for `n >= 1`. -/
def Bz (z : ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else z ^ ω n, rfl⟩

theorem Bz_apply (z : ℤ) {n : ℕ} (hn : n ≠ 0) : Bz z n = z ^ ω n := by
  show (if n = 0 then 0 else z ^ ω n) = _
  rw [if_neg hn]

theorem Bz_mult (z : ℤ) : (Bz z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [Bz_apply z one_ne_zero, cardDistinctFactors_one, pow_zero], ?_⟩
  intro m n hm hn hmn
  rw [Bz_apply z (mul_ne_zero hm hn), Bz_apply z hm, Bz_apply z hn,
    cardDistinctFactors_mul hmn, pow_add]

theorem Bz_prime (z : ℤ) {q : ℕ} (hq : q.Prime) : Bz z q = z := by
  rw [Bz_apply z hq.ne_zero, cardDistinctFactors_apply_prime hq, pow_one]

/-! ## 2. Inverse cores and the corrections -/

/-- The Dirichlet inverse of `zpowZeta z`. -/
noncomputable def zinv (z : ℤ) : ArithmeticFunction ℤ :=
  if 0 ≤ z then (μ : ArithmeticFunction ℤ) ^ z.toNat else (ζ : ArithmeticFunction ℤ) ^ z.natAbs

theorem zpowZeta_mul_zinv (z : ℤ) : zpowZeta z * zinv z = 1 := by
  unfold zpowZeta zinv
  split_ifs
  · rw [← mul_pow, coe_zeta_mul_moebius, one_pow]
  · rw [← mul_pow, moebius_mul_coe_zeta, one_pow]

theorem zinv_mult (z : ℤ) : (zinv z).IsMultiplicative := by
  unfold zinv
  split_ifs
  · exact isMultiplicative_moebius.pow
  · exact isMultiplicative_zeta.natCast.pow

theorem zinv_prime (z : ℤ) {q : ℕ} (hq : q.Prime) : zinv z q = -z := by
  unfold zinv
  split_ifs with hz
  · rw [pow_apply_prime' (by simp) _ hq, moebius_apply_prime hq]; omega
  · rw [pow_apply_prime' zeta_int_one _ hq, zeta_int_prime hq, mul_one]; omega

/-- The squarefull correction `h_z = (zpowZeta z)⁻¹ * B_z` (integral). -/
noncomputable def hcorr (z : ℤ) : ArithmeticFunction ℤ := zinv z * Bz z

theorem core_mul_hcorr (z : ℤ) : zpowZeta z * hcorr z = Bz z := by
  rw [hcorr, ← mul_assoc, zpowZeta_mul_zinv, one_mul]

theorem hcorr_mult (z : ℤ) : (hcorr z).IsMultiplicative := (zinv_mult z).mul (Bz_mult z)

theorem hcorr_one (z : ℤ) : hcorr z 1 = 1 := (hcorr_mult z).map_one

theorem hcorr_prime (z : ℤ) {q : ℕ} (hq : q.Prime) : hcorr z q = 0 := by
  rw [hcorr, FrobLevel.Dir.mul_apply_prime _ _ hq, (zinv_mult z).map_one, (Bz_mult z).map_one,
    Bz_prime z hq, zinv_prime z hq]
  ring

/-- **Squarefull support.** `h_z(n) = 0` whenever some prime divides `n` exactly once. -/
theorem hcorr_squarefull (z : ℤ) {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hq2 : ¬ q ^ 2 ∣ n) :
    hcorr z n = 0 := by
  obtain ⟨m, rfl⟩ := hqn
  have hcop : q.Coprime m := by
    rw [hq.coprime_iff_not_dvd]
    rintro ⟨l, rfl⟩
    exact hq2 ⟨l, by ring⟩
  rw [(hcorr_mult z).map_mul_of_coprime hcop, hcorr_prime z hq, zero_mul]

/-- `h_z` vanishes on squarefree `m > 1`. -/
theorem hcorr_squarefree (z : ℤ) {m : ℕ} (hm : Squarefree m) (hm1 : 1 < m) : hcorr z m = 0 := by
  rw [apply_squarefree_of_mult (hcorr_mult z) hm (fun q hq _ => hcorr_prime z hq)]
  exact zero_pow (Nat.pos_iff_ne_zero.mp (cardDistinctFactors_pos.mpr hm1))

/-! ## 3. The construction, pointwise on all `n` -/

/-- The construction `F = sum over z of a_z (zpowZeta z * h_z)` equals
`sum over z of a_z z ^ omega(n)` at every `n >= 1`. -/
theorem fam_hcorr_apply (T : Finset ℤ) (a : ℤ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    fam T a zpowZeta hcorr n = mom T a (ω n) := by
  rw [fam_apply, mom]
  apply sum_congr rfl
  intro z _
  rw [core_mul_hcorr, Bz_apply z hn]

theorem agg_hcorr (a : ℤ → ℤ) : agg a hcorr = a := by
  funext z; rw [agg, hcorr_one, mul_one]

section Exact

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Construction (explicit).** For a nonempty node set `T` without `0` with `p^k | prod T`
there are integer weights `a`, and `C = p^v u` with `p` not dividing `u`, such that
`F = fam T a zpowZeta hcorr` satisfies: `F n = sum over z of a_z z^omega(n)` for `n >= 1`;
`F(q^e) = C` at every prime power `q^e`, `e >= 1`; `C p^k | F n` whenever `omega(n) >= 2`. -/
theorem construction_explicit {k : ℕ} (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (hne : T.Nonempty)
    (hk : (p : ℤ) ^ k ∣ ∏ z ∈ T, z) :
    ∃ a : ℤ → ℤ, ∃ C : ℤ, ∃ v : ℕ, ∃ u : ℤ, C = p ^ v * u ∧ ¬ (p : ℤ) ∣ u ∧
      (∀ n, n ≠ 0 → fam T a zpowZeta hcorr n = mom T a (ω n)) ∧
      (∀ q e, q.Prime → 1 ≤ e → fam T a zpowZeta hcorr (q ^ e) = C) ∧
      (∀ n, 2 ≤ ω n → C * (p : ℤ) ^ k ∣ fam T a zpowZeta hcorr n) := by
  obtain ⟨a, hC, hr⟩ := construct_moment T h0 hne
  set C := mom T a 1
  set v := padicValInt p C
  have hvC : (p : ℤ) ^ v ∣ C := padicValInt_dvd C
  refine ⟨a, C, v, C / p ^ v, (Int.mul_ediv_cancel' hvC).symm, ?_, fun n hn =>
    fam_hcorr_apply T a hn, ?_, ?_⟩
  · intro hu
    have h2 : (p : ℤ) ^ (v + 1) ∣ C := by
      rw [← Int.mul_ediv_cancel' hvC, pow_succ]; exact mul_dvd_mul_left _ hu
    rcases (padicValInt_dvd_iff (v + 1) C).1 h2 with h | h
    · exact hC h
    · omega
  · intro q e hq he
    rw [fam_hcorr_apply T a (pow_ne_zero _ hq.ne_zero),
      cardDistinctFactors_apply_prime_pow hq (by omega)]
  · intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [fam_hcorr_apply T a hn0]
    exact (mul_dvd_mul_left C hk).trans (hr _ hn)

omit hp in
/-- The constructed member meets the target. -/
theorem targetD_of_momentTarget {k : ℕ} (T : Finset ℤ) (a : ℤ → ℤ)
    (h : MomentTarget p k T a) : ∃ v, TargetD p v k (fam T a zpowZeta hcorr) := by
  obtain ⟨v, u, hu, h1, hr⟩ := h
  refine ⟨v, fun q hq => ⟨u, hu, ?_⟩, fun n hn => ?_⟩
  · rw [fam_hcorr_apply T a hq.ne_zero, cardDistinctFactors_apply_prime hq]; exact h1
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [fam_hcorr_apply T a hn0]; exact hr _ hn

/-- The family with cheap nodes (cores `zeta ^ z`, `z` in `{1..Z}`) meets `TargetD p v k`
for some `v`. -/
def CheapAchievable (k Z : ℕ) : Prop :=
  ∃ T ⊆ cheapNodes Z, ∃ c : ℤ → ℤ, ∃ h : ℤ → ArithmeticFunction ℤ,
    (∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0) ∧ ∃ v, TargetD p v k (fam T c zpowZeta h)

/-- The family with signed nodes (cores `zeta ^ z` and `moebius ^ |z|`, `z` in
`{-Z..-1} union {1..Z}`) meets `TargetD p v k` for some `v`. -/
def SignedAchievable (k Z : ℕ) : Prop :=
  ∃ T ⊆ signedNodes Z, ∃ c : ℤ → ℤ, ∃ h : ℤ → ArithmeticFunction ℤ,
    (∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0) ∧ ∃ v, TargetD p v k (fam T c zpowZeta h)

/-- **Theorem H, cheap (exact).** For `k >= 1`: achievable with nodes in `{1..Z}` iff
`S(p^k) <= Z`. -/
theorem cheap_arith_iff {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    CheapAchievable p k Z ↔ FrobLevel.kempner p k ≤ Z := by
  constructor
  · rintro ⟨T, hT, c, h, hh, v, hf⟩
    exact cheap_arith_lower p T hT c h hh hf
  · intro hZ
    obtain ⟨T, hT, a, ha⟩ := (cheap_moment_iff p hk Z).2 hZ
    exact ⟨T, hT, a, hcorr, fun z _ m hm hm1 => hcorr_squarefree z hm hm1,
      targetD_of_momentTarget p T a ha⟩

/-- **Theorem H, signed (exact).** For `k >= 1`: achievable with nodes in
`{-Z..-1} union {1..Z}` iff `S(p^ceil(k/2)) <= Z`. -/
theorem signed_arith_iff {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    SignedAchievable p k Z ↔ FrobLevel.kempner p ((k + 1) / 2) ≤ Z := by
  constructor
  · rintro ⟨T, hT, c, h, hh, v, hf⟩
    exact signed_arith_lower p T hT c h hh hf
  · intro hZ
    obtain ⟨T, hT, a, ha⟩ := (signed_moment_iff p hk Z).2 hZ
    exact ⟨T, hT, a, hcorr, fun z _ m hm hm1 => hcorr_squarefree z hm hm1,
      targetD_of_momentTarget p T a ha⟩

/-- **(H2)** `Z_cheap(p, k) = S(p^k)`. -/
theorem Zcheap_eq {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievable p k Z} (FrobLevel.kempner p k) :=
  ⟨(cheap_arith_iff p hk _).2 le_rfl, fun _ hZ => (cheap_arith_iff p hk _).1 hZ⟩

/-- **(H1)** `Z_signed(p, k) = S(p^ceil(k/2))`. -/
theorem Zsigned_eq {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | SignedAchievable p k Z} (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨(signed_arith_iff p hk _).2 le_rfl, fun _ hZ => (signed_arith_iff p hk _).1 hZ⟩

end Exact

end M2L
