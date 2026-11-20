/-
Run r25 / M2, seat M2L2 (item 5): the summatory identities (H9) and (H10) of A19 (Q5 section 10).

Notation: `π = Nat.primeCounting` (number of primes `<= n`), `⌊y⌋₊ = Nat.floor`,
`x ^ (1 / j)` the real power, `Nat.log 2 x = ⌊log_2 x⌋`.

Contents.
1. `card_primePow_eq`: the number of prime powers `q ^ e` (`e >= 1`) in `[1, x]` is
   `sum over j in [1, log_2 x] of π(⌊x ^ (1/j)⌋₊)`.
2. `sum_eq_mod` (general): if `f(q^e) = C` at every prime power and `D | f n` whenever
   `omega(n) >= 2`, then for `x >= 1`:
   `D | sum over n in [1, x] of f n - (f 1 + C * sum over j in [1, log_2 x] of π(⌊x^(1/j)⌋₊))`.
3. `H9_H10`: for every nonempty node set `T` without `0` with `p^k | prod T` there are integer
   weights `a`, `C = p^v u` (`p` not dividing `u`) such that `F = fam T a zpowZeta hcorr`
   (`F(n) = sum a_z z^omega(n)`) satisfies, for every integer `x >= 1`,
   (H9) `sum_{n <= x} F(n) = sum_z a_z + C sum_{j=1}^{⌊log_2 x⌋} π(⌊x^(1/j)⌋) (mod C p^k)`,
   (H10) `C | sum_{n <= x} F(n) - sum_z a_z` and
   `π(x) = (sum_{n <= x} F(n) - sum_z a_z) / C - sum_{j=2}^{⌊log_2 x⌋} π(⌊x^(1/j)⌋) (mod p^k)`.
   `H9_H10_cheap`, `H9_H10_signed`: the same on the node sets `{1..Z}` with `S(p^k) <= Z` and
   `{-Z..Z} \ {0}` with `S(p^ceil(k/2)) <= Z`.

Lean v4.33.1 with Mathlib; imports the r25 library and round 1.
-/
import Mathlib
import Found
import DirBase
import DirMain
import Moment
import MomentZ
import Slice
import Construct

namespace M2L2

open Finset ArithmeticFunction M2L
open scoped ArithmeticFunction.omega

/-! ## 1. Counting prime powers -/

/-- Primes `q <= x` with `q ^ j <= x`. -/
def primesPowLe (x j : ℕ) : Finset ℕ := (range (x + 1)).filter fun q => q.Prime ∧ q ^ j ≤ x

theorem le_floor_rpow_iff {x j q : ℕ} (hj : 1 ≤ j) :
    q ≤ ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ ↔ q ^ j ≤ x := by
  have hx : (0 : ℝ) ≤ (x : ℝ) ^ (1 / (j : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg x) _
  rw [Nat.le_floor_iff hx, one_div, Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg q)
    (Nat.cast_nonneg x) (by exact_mod_cast hj), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

theorem card_primesPowLe {x j : ℕ} (hj : 1 ≤ j) :
    (primesPowLe x j).card = Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow]
  congr 1
  ext q
  simp only [primesPowLe, mem_filter, mem_range]
  constructor
  · rintro ⟨_, hq, hqx⟩
    exact ⟨Nat.lt_succ_of_le ((le_floor_rpow_iff hj).2 hqx), hq⟩
  · rintro ⟨hqR, hq⟩
    have hqx := (le_floor_rpow_iff hj).1 (Nat.lt_succ_iff.mp hqR)
    exact ⟨Nat.lt_succ_of_le ((Nat.le_self_pow (by omega) q).trans hqx), hq, hqx⟩

/-- Prime powers `q ^ e` (`e >= 1`) in `[1, x]`. -/
def primePowLe (x : ℕ) : Finset ℕ := (Icc 1 x).filter IsPrimePow

theorem primePowLe_eq (x : ℕ) :
    primePowLe x = (Icc 1 (Nat.log 2 x)).biUnion fun j => (primesPowLe x j).image (· ^ j) := by
  ext n
  simp only [primePowLe, primesPowLe, mem_filter, mem_Icc, mem_biUnion, mem_image, mem_range,
    isPrimePow_nat_iff]
  constructor
  · rintro ⟨⟨hn1, hnx⟩, q, e, hq, he, rfl⟩
    refine ⟨e, ⟨he, Nat.le_log_of_pow_le (by norm_num)
      ((Nat.pow_le_pow_left hq.two_le e).trans hnx)⟩, q, ⟨Nat.lt_succ_of_le
        ((Nat.le_self_pow (by omega) q).trans hnx), hq, hnx⟩, rfl⟩
  · rintro ⟨j, ⟨hj, _⟩, q, ⟨_, hq, hqx⟩, rfl⟩
    exact ⟨⟨Nat.one_le_pow _ _ hq.pos, hqx⟩, q, j, hq, hj, rfl⟩

/-- **Prime powers up to `x`.** `#{q^e <= x : e >= 1} = sum_{j=1}^{⌊log_2 x⌋} π(⌊x^(1/j)⌋)`. -/
theorem card_primePow_eq (x : ℕ) :
    (primePowLe x).card =
      ∑ j ∈ Icc 1 (Nat.log 2 x), Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ := by
  rw [primePowLe_eq, card_biUnion]
  · apply sum_congr rfl
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    rw [card_image_of_injOn (fun a _ b _ h => Nat.pow_left_injective (by omega) h),
      card_primesPowLe hj1]
  · intro j hj j' hj' hne
    rw [Function.onFun, disjoint_left]
    intro n hn hn'
    obtain ⟨q, hqm, rfl⟩ := mem_image.mp hn
    obtain ⟨q', hqm', he⟩ := mem_image.mp hn'
    have hq := (mem_filter.mp hqm).2.1
    have hq' := (mem_filter.mp hqm').2.1
    have hj1 := (mem_Icc.mp (mem_coe.mp hj)).1
    have hj1' := (mem_Icc.mp (mem_coe.mp hj')).1
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', j' = m' + 1 := ⟨j' - 1, by omega⟩
    exact hne (by rw [(Nat.Prime.pow_inj hq' hq he).2])

/-! ## 2. The summatory congruence for a function constant on prime powers -/

theorem two_le_omega {n : ℕ} (hn : 2 ≤ n) (hpp : ¬ IsPrimePow n) : 2 ≤ ω n := by
  have h0 : ω n ≠ 0 := fun h => by have := cardDistinctFactors_eq_zero.mp h; omega
  have h1 : ω n ≠ 1 := fun h => hpp (cardDistinctFactors_eq_one_iff.mp h)
  omega

/-- **Summatory congruence (general).** If `f(q^e) = C` at every prime power and `D | f n`
whenever `omega(n) >= 2`, then for `x >= 1`,
`D | sum_{n in [1,x]} f n - (f 1 + C * sum_{j=1}^{⌊log_2 x⌋} π(⌊x^(1/j)⌋₊))`. -/
theorem sum_eq_mod (f : ArithmeticFunction ℤ) (C D : ℤ)
    (hpp : ∀ q e : ℕ, q.Prime → 1 ≤ e → f (q ^ e) = C) (hcomp : ∀ n, 2 ≤ ω n → D ∣ f n)
    {x : ℕ} (hx : 1 ≤ x) :
    D ∣ ∑ n ∈ Icc 1 x, f n - (f 1 + C *
      ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ)) := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 x) IsPrimePow]
  have hP : ∑ n ∈ (Icc 1 x).filter IsPrimePow, f n = C * (primePowLe x).card := by
    rw [primePowLe, sum_congr rfl (g := fun _ => C), sum_const, nsmul_eq_mul, mul_comm]
    intro n hn
    obtain ⟨q, e, hq, he, rfl⟩ := (isPrimePow_nat_iff n).mp (mem_filter.mp hn).2
    exact hpp q e hq he
  have h1 : 1 ∈ (Icc 1 x).filter (fun n => ¬ IsPrimePow n) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hx⟩, not_isPrimePow_one⟩
  rw [hP, ← add_sum_erase _ _ h1, card_primePow_eq]
  push_cast
  have hrest : D ∣ ∑ n ∈ ((Icc 1 x).filter fun n => ¬ IsPrimePow n).erase 1, f n :=
    dvd_sum fun n hn => by
      obtain ⟨hn1, hn⟩ := mem_erase.mp hn
      obtain ⟨hnI, hnp⟩ := mem_filter.mp hn
      exact hcomp n (two_le_omega (by have := (mem_Icc.mp hnI).1; omega) hnp)
  have e : C * ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ) +
      (f 1 + ∑ n ∈ ((Icc 1 x).filter fun n => ¬ IsPrimePow n).erase 1, f n) -
      (f 1 + C * ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ)) =
      ∑ n ∈ ((Icc 1 x).filter fun n => ¬ IsPrimePow n).erase 1, f n := by ring
  rw [e]; exact hrest

theorem floor_rpow_one (x : ℕ) : ⌊(x : ℝ) ^ (1 / ((1 : ℕ) : ℝ))⌋₊ = x := by
  simp

/-- Splitting off `j = 1`: the `j`-sum is `π(x) + sum_{j=2}^{⌊log_2 x⌋}` (for `x >= 1`). -/
theorem sum_split_one {x : ℕ} (hx : 1 ≤ x) :
    ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ) =
      Nat.primeCounting x +
        ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ) := by
  rcases Nat.eq_zero_or_pos (Nat.log 2 x) with hL | hL
  · have hx2 : x < 2 := by
      by_contra h
      have := Nat.le_log_of_pow_le (b := 2) (x := 1) (y := x) (by norm_num) (by omega)
      omega
    have : x = 1 := by omega
    subst this
    rw [hL]
    simp
  · have e : Icc 1 (Nat.log 2 x) = insert 1 (Icc 2 (Nat.log 2 x)) := by
      ext j; simp only [mem_insert, mem_Icc]; omega
    rw [e, sum_insert (by simp), floor_rpow_one]

/-! ## 3. (H9) and (H10) for the construction -/

section H910

variable (p : ℕ) [hp : Fact p.Prime]

/-- **(H9) and (H10).** For a nonempty node set `T` without `0` with `p^k | prod T` there are
integer weights `a` and `C = p^v u` (`p` not dividing `u`) such that `F = fam T a zpowZeta hcorr`
satisfies, for every `x >= 1`:
(H9) `C p^k | sum_{n=1}^{x} F(n) - (sum_z a_z + C sum_{j=1}^{⌊log_2 x⌋} π(⌊x^(1/j)⌋))`;
(H10) `C | sum_{n=1}^{x} F(n) - sum_z a_z` and
`p^k | (sum_{n=1}^{x} F(n) - sum_z a_z) / C - sum_{j=2}^{⌊log_2 x⌋} π(⌊x^(1/j)⌋) - π(x)`. -/
theorem H9_H10 {k : ℕ} (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (hne : T.Nonempty)
    (hk : (p : ℤ) ^ k ∣ ∏ z ∈ T, z) :
    ∃ a : ℤ → ℤ, ∃ C : ℤ, ∃ v : ℕ, ∃ u : ℤ, C = p ^ v * u ∧ ¬ (p : ℤ) ∣ u ∧
      (∀ n, n ≠ 0 → fam T a zpowZeta hcorr n = ∑ z ∈ T, a z * z ^ ω n) ∧
      (∀ x : ℕ, 1 ≤ x → C * (p : ℤ) ^ k ∣ ∑ n ∈ Icc 1 x, fam T a zpowZeta hcorr n -
        (∑ z ∈ T, a z + C * ∑ j ∈ Icc 1 (Nat.log 2 x),
          (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ))) ∧
      (∀ x : ℕ, 1 ≤ x → C ∣ ∑ n ∈ Icc 1 x, fam T a zpowZeta hcorr n - ∑ z ∈ T, a z ∧
        (p : ℤ) ^ k ∣ (∑ n ∈ Icc 1 x, fam T a zpowZeta hcorr n - ∑ z ∈ T, a z) / C -
          ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ) -
          Nat.primeCounting x) := by
  obtain ⟨a, C, v, u, hC, hu, hF, hpp, hcomp⟩ := construction_explicit p T h0 hne hk
  have hF1 : fam T a zpowZeta hcorr 1 = ∑ z ∈ T, a z := by
    rw [hF 1 one_ne_zero, mom, cardDistinctFactors_one]; simp
  have hC0 : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
      (fun h => hu (h ▸ dvd_zero _))
  have H9 : ∀ x : ℕ, 1 ≤ x → C * (p : ℤ) ^ k ∣ ∑ n ∈ Icc 1 x, fam T a zpowZeta hcorr n -
      (∑ z ∈ T, a z + C * ∑ j ∈ Icc 1 (Nat.log 2 x),
        (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ)) := by
    intro x hx
    rw [← hF1]
    exact sum_eq_mod _ C (C * (p : ℤ) ^ k) hpp hcomp hx
  refine ⟨a, C, v, u, hC, hu, fun n hn => by rw [hF n hn]; rfl, H9, fun x hx => ?_⟩
  have h9 := H9 x hx
  rw [sum_split_one hx] at h9
  set S := ∑ n ∈ Icc 1 x, fam T a zpowZeta hcorr n
  set A := ∑ z ∈ T, a z
  set R := ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ)
  have hdiv : C ∣ S - A := by
    have := dvd_add ((dvd_mul_right C _).trans h9)
      (dvd_mul_right C ((Nat.primeCounting x : ℤ) + R))
    have e : S - (A + C * ((Nat.primeCounting x : ℤ) + R)) + C * ((Nat.primeCounting x : ℤ) + R)
      = S - A := by ring
    rwa [e] at this
  refine ⟨hdiv, ?_⟩
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, Int.mul_ediv_cancel_left _ hC0]
  have e : S - (A + C * ((Nat.primeCounting x : ℤ) + R)) = C * (Q - R - Nat.primeCounting x) := by
    rw [show S = (S - A) + A by ring, hQ]; ring
  rw [e] at h9
  exact (mul_dvd_mul_iff_left hC0).1 h9

/-- (H9), (H10) on the cheap node set `{1..Z}` with `S(p^k) <= Z`. -/
theorem H9_H10_cheap {k Z : ℕ} (hk : 1 ≤ k) (hZ : FrobLevel.kempner p k ≤ Z) :
    ∃ a : ℤ → ℤ, ∃ C : ℤ, ∃ v : ℕ, ∃ u : ℤ, C = p ^ v * u ∧ ¬ (p : ℤ) ∣ u ∧
      (∀ x : ℕ, 1 ≤ x → C * (p : ℤ) ^ k ∣ ∑ n ∈ Icc 1 x, fam (cheapNodes Z) a zpowZeta hcorr n -
        (∑ z ∈ cheapNodes Z, a z + C * ∑ j ∈ Icc 1 (Nat.log 2 x),
          (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ))) ∧
      (∀ x : ℕ, 1 ≤ x → C ∣ ∑ n ∈ Icc 1 x, fam (cheapNodes Z) a zpowZeta hcorr n -
          ∑ z ∈ cheapNodes Z, a z ∧
        (p : ℤ) ^ k ∣ (∑ n ∈ Icc 1 x, fam (cheapNodes Z) a zpowZeta hcorr n -
          ∑ z ∈ cheapNodes Z, a z) / C -
          ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ) -
          Nat.primeCounting x) := by
  have hZ1 : 1 ≤ Z := (FrobLevel.kempner_pos p hk).trans hZ
  have hdiv : (p : ℤ) ^ k ∣ ∏ z ∈ cheapNodes Z, z := by
    rw [pow_dvd_prod_iff p _ (zero_not_mem_cheap Z), sum_val_cheap]
    exact kempner_dvd_factorial p hZ
  obtain ⟨a, C, v, u, hC, hu, -, h9, h10⟩ := H9_H10 p (cheapNodes Z) (zero_not_mem_cheap Z)
    ⟨1, by simp [cheapNodes]; omega⟩ hdiv
  exact ⟨a, C, v, u, hC, hu, h9, h10⟩

/-- (H9), (H10) on the signed node set `{-Z..-1} union {1..Z}` with `S(p^ceil(k/2)) <= Z`. -/
theorem H9_H10_signed {k Z : ℕ} (hk : 1 ≤ k) (hZ : FrobLevel.kempner p ((k + 1) / 2) ≤ Z) :
    ∃ a : ℤ → ℤ, ∃ C : ℤ, ∃ v : ℕ, ∃ u : ℤ, C = p ^ v * u ∧ ¬ (p : ℤ) ∣ u ∧
      (∀ x : ℕ, 1 ≤ x → C * (p : ℤ) ^ k ∣ ∑ n ∈ Icc 1 x, fam (signedNodes Z) a zpowZeta hcorr n -
        (∑ z ∈ signedNodes Z, a z + C * ∑ j ∈ Icc 1 (Nat.log 2 x),
          (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ))) ∧
      (∀ x : ℕ, 1 ≤ x → C ∣ ∑ n ∈ Icc 1 x, fam (signedNodes Z) a zpowZeta hcorr n -
          ∑ z ∈ signedNodes Z, a z ∧
        (p : ℤ) ^ k ∣ (∑ n ∈ Icc 1 x, fam (signedNodes Z) a zpowZeta hcorr n -
          ∑ z ∈ signedNodes Z, a z) / C -
          ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting ⌊(x : ℝ) ^ (1 / (j : ℝ))⌋₊ : ℤ) -
          Nat.primeCounting x) := by
  have hZ1 : 1 ≤ Z := (FrobLevel.kempner_pos p (by omega)).trans hZ
  have hdiv : (p : ℤ) ^ k ∣ ∏ z ∈ signedNodes Z, z := by
    rw [pow_dvd_prod_iff p _ (zero_not_mem_signed Z), sum_val_signed]
    have := kempner_dvd_factorial p hZ
    omega
  obtain ⟨a, C, v, u, hC, hu, -, h9, h10⟩ := H9_H10 p (signedNodes Z) (zero_not_mem_signed Z)
    ⟨1, by simp [signedNodes]; omega⟩ hdiv
  exact ⟨a, C, v, u, hC, hu, h9, h10⟩

end H910

end M2L2
