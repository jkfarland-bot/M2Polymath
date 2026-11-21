module

public import Mathlib

/-!
  Seat M2L3, item 6: the elementary inequality behind the Theorem G gap (A19 section 8;
  Lelechenko arXiv:1305.1639v3, proof of Theorem 5, page 9).
  The proof uses ∑_{d ≤ U} d^(-b k1/k2) ≪ U^(1 - b k1/k2). When b k1 > k2 the exponent
  s = b k1/k2 exceeds 1, the sum is at least 1 (its d = 1 term), and U^(1 - s) → 0, so no
  constant C gives the bound for all U. The parameter arithmetic of the mod 3 counterexample
  (mu with k1 = 3, a = 2/3; d_3 with k2 = 1, b = 3/5) is checked exactly.
-/

@[expose] public section

open Finset Filter Topology

namespace M2L3

/-- The power sum is at least its `d = 1` term. -/
theorem powsum_ge_one (s : ℝ) {U : ℕ} (hU : 1 ≤ U) :
    1 ≤ ∑ d ∈ Icc 1 U, (d : ℝ) ^ (-s) := by
  have h1 : (1 : ℕ) ∈ Icc 1 U := mem_Icc.2 ⟨le_rfl, hU⟩
  calc (1 : ℝ) = ((1 : ℕ) : ℝ) ^ (-s) := by simp
    _ ≤ ∑ d ∈ Icc 1 U, (d : ℝ) ^ (-s) :=
      single_le_sum (f := fun d : ℕ => (d : ℝ) ^ (-s))
        (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) h1

/-- **The gap.** If `s > 1` there is no constant `C` with
`∑_{d ≤ U} d^(-s) ≤ C U^(1 - s)` for every `U ≥ 1`. -/
theorem powsum_bound_fails {s : ℝ} (hs : 1 < s) (C : ℝ) :
    ¬ ∀ U : ℕ, 1 ≤ U → ∑ d ∈ Icc 1 U, (d : ℝ) ^ (-s) ≤ C * (U : ℝ) ^ (1 - s) := by
  intro hbound
  have ht : Tendsto (fun U : ℕ => C * (U : ℝ) ^ (1 - s)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (-(s - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have h1 := (h0.comp tendsto_natCast_atTop_atTop).const_mul C
    simp only [mul_zero] at h1
    refine h1.congr fun U => ?_
    simp [Function.comp, neg_sub]
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).and
    (eventually_ge_atTop 1)
  obtain ⟨U, hlt, hU⟩ := hev.exists
  have := hbound U hU
  have := powsum_ge_one s hU
  linarith

/-- The same statement in Lelechenko's parameters: if `b k1 > k2 > 0` then
`∑_{d ≤ U} d^(-b k1/k2) ≪ U^(1 - b k1/k2)` fails. -/
theorem lelechenko_step_fails {b k1 k2 : ℝ} (hk2 : 0 < k2) (hgap : k2 < b * k1) (C : ℝ) :
    ¬ ∀ U : ℕ, 1 ≤ U →
      ∑ d ∈ Icc 1 U, (d : ℝ) ^ (-(b * k1 / k2)) ≤ C * (U : ℝ) ^ (1 - b * k1 / k2) :=
  powsum_bound_fails (by rw [lt_div_iff₀ hk2]; linarith) C

/-- The printed bound for the mod 3 substitution: `x^(3/5) ≤ C x^(9/23)` fails for large `x`
(the ratio is `x^(24/115)`). -/
theorem printed_bound_fails (C : ℝ) :
    ¬ ∀ x : ℝ, 1 ≤ x → x ^ ((3 : ℝ) / 5) ≤ C * x ^ ((9 : ℝ) / 23) := by
  intro h
  have ht : Tendsto (fun x : ℝ => x ^ ((24 : ℝ) / 115)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨x, hx, hx1⟩ := ((ht.eventually_gt_atTop C).and (eventually_ge_atTop 1)).exists
  have hpos : 0 < x ^ ((9 : ℝ) / 23) := Real.rpow_pos_of_pos (by linarith) _
  have hsplit : x ^ ((3 : ℝ) / 5) = x ^ ((24 : ℝ) / 115) * x ^ ((9 : ℝ) / 23) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have := h x hx1
  rw [hsplit] at this
  have := le_of_mul_le_mul_right this hpos
  linarith

/-- The first work sum `x^(3/5) ∑_{d ≤ U} d^(-9/5)` is at least `x^(3/5)` for every `U ≥ 1`. -/
theorem first_work_sum_ge (x : ℝ) (hx : 0 ≤ x) {U : ℕ} (hU : 1 ≤ U) :
    x ^ ((3 : ℝ) / 5) ≤ x ^ ((3 : ℝ) / 5) * ∑ d ∈ Icc 1 U, (d : ℝ) ^ (-((9 : ℝ) / 5)) :=
  le_mul_of_one_le_right (Real.rpow_nonneg hx _) (powsum_ge_one _ hU)

/-- Parameter arithmetic of the counterexample: `k1 = 3, a = 2/3, k2 = 1, b = 3/5`.
`a + b < 2`; `b k1 / k2 = 9/5 > 1`; Lelechenko's cutoff `c = 18/23`; the printed exponent
`(1 - a b)/((1 - a) k2 + (1 - b) k1) = 9/23`; the safe bound (G2) `max(a/k1, b/k2, 9/23) = 3/5`. -/
theorem counterexample_parameters :
    let a : ℚ := 2 / 3; let b : ℚ := 3 / 5; let k1 : ℚ := 3; let k2 : ℚ := 1
    a + b < 2 ∧ b * k1 / k2 = 9 / 5 ∧ 1 < b * k1 / k2 ∧
    (1 - b) * k1 / ((1 - a) * k2 + (1 - b) * k1) = 18 / 23 ∧
    (1 - a * b) / ((1 - a) * k2 + (1 - b) * k1) = 9 / 23 ∧
    max (max (a / k1) (b / k2)) ((1 - a * b) / ((1 - a) * k2 + (1 - b) * k1)) = 3 / 5 := by
  norm_num

end M2L3
