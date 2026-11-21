module

public import Mathlib
public import M2Ternary

/-!
  Seat M2L4, item 2: the incomplete-sum axis swap of the M2d-v report (section 1(b)),
  for every y and every lower limit a, and (F1) evaluated with it equals D_3, for every x.
  All divisions are natural-number floor divisions; the identity is stated over the integers.
-/

@[expose] public section

open Finset

namespace M2L4
open M2L3

/-- `r = ⌊√y⌋`. -/
abbrev sw_r (y : ℕ) : ℕ := Nat.sqrt y

/-- `c = min (max (a - 1) ⌊y^(1/3)⌋) r`. -/
def sw_c (y a : ℕ) : ℕ := min (max (a - 1) (icbrt y)) (Nat.sqrt y)

/-- `M = ⌊y / (c + 1)⌋`. -/
def sw_M (y a : ℕ) : ℕ := y / (sw_c y a + 1)

lemma floor_div_as_count (y b : ℕ) (hb : 0 < b) :
    y / b = ∑ t ∈ Ioc 0 y, (if b * t ≤ y then 1 else 0) := by
  rw [sum_boole, Nat.cast_id]
  have : (Ioc 0 y).filter (fun t => b * t ≤ y) = Ioc 0 (y / b) := by
    ext t
    simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le hb]
    constructor
    · rintro ⟨⟨h0, _⟩, h⟩; exact ⟨h0, by rw [mul_comm]; exact h⟩
    · rintro ⟨h0, h⟩
      refine ⟨⟨h0, ?_⟩, by rw [mul_comm]; exact h⟩
      exact (Nat.le_mul_of_pos_right t hb).trans h
  rw [this, Nat.card_Ioc, Nat.sub_zero]

lemma div_le_sqrt_of_gt {y t : ℕ} (ht : Nat.sqrt y < t) : y / t ≤ Nat.sqrt y := by
  have h1 := Nat.lt_succ_sqrt y
  have : y < t * (Nat.sqrt y + 1) :=
    lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ ht)
  exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [mul_comm]; exact this))

/-- The lattice-point core of the swap, in natural numbers, for every `c ≤ ⌊√y⌋`:
`∑_{c < b ≤ r} ⌊y/b⌋ + c (M - r) = r (r - c) + ∑_{r < t ≤ M} ⌊y/t⌋` with `M = ⌊y/(c+1)⌋`
(natural subtraction `M - r`, which is `0` when `M < r`). -/
theorem swap_core (y c : ℕ) (hc : c ≤ Nat.sqrt y) :
    ∑ b ∈ Ioc c (Nat.sqrt y), y / b + c * (y / (c + 1) - Nat.sqrt y)
      = Nat.sqrt y * (Nat.sqrt y - c) + ∑ t ∈ Ioc (Nat.sqrt y) (y / (c + 1)), y / t := by
  set r := Nat.sqrt y with hr
  have hrr : r * r ≤ y := Nat.sqrt_le y
  have hry : r ≤ y := Nat.sqrt_le_self y
  -- write each `⌊y/b⌋` as a count over `t ∈ (0, y]`, split at `t = r`
  have e1 : ∑ b ∈ Ioc c r, y / b = ∑ b ∈ Ioc c r, ∑ t ∈ Ioc 0 r, (if b * t ≤ y then 1 else 0)
      + ∑ t ∈ Ioc r y, ∑ b ∈ Ioc c r, (if b * t ≤ y then 1 else 0) := by
    rw [sum_comm (s := Ioc r y), ← sum_add_distrib]
    refine sum_congr rfl fun b hb => ?_
    rw [floor_div_as_count y b (by have := (mem_Ioc.1 hb).1; omega),
      sum_Ioc_consecutive _ (Nat.zero_le r) hry]
  have e2 : ∑ b ∈ Ioc c r, ∑ t ∈ Ioc 0 r, (if b * t ≤ y then 1 else 0) = r * (r - c) := by
    have : ∀ b ∈ Ioc c r, ∑ t ∈ Ioc 0 r, (if b * t ≤ y then 1 else 0) = r := by
      intro b hb
      rw [sum_congr rfl (g := fun _ => 1), sum_const, Nat.card_Ioc, smul_eq_mul, mul_one,
        Nat.sub_zero]
      intro t ht
      rw [ite_eq_left]
      exact (Nat.mul_le_mul (mem_Ioc.1 hb).2 (mem_Ioc.1 ht).2).trans hrr
    rw [sum_congr rfl this, sum_const, Nat.card_Ioc, smul_eq_mul, mul_comm]
  have e3 : ∀ t ∈ Ioc r y, ∑ b ∈ Ioc c r, (if b * t ≤ y then 1 else 0) = y / t - c := by
    intro t ht
    have ht0 : 0 < t := by have := (mem_Ioc.1 ht).1; omega
    have hdl := div_le_sqrt_of_gt (mem_Ioc.1 ht).1
    rw [sum_boole, Nat.cast_id]
    have : (Ioc c r).filter (fun b => b * t ≤ y) = Ioc c (y / t) := by
      ext b
      simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le ht0]
      constructor
      · rintro ⟨⟨h0, _⟩, h⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩
        exact ⟨⟨h0, (Nat.le_div_iff_mul_le ht0).2 h |>.trans hdl⟩, h⟩
    rw [this, Nat.card_Ioc]
  have hMy : y / (c + 1) ≤ y := Nat.div_le_self _ _
  have e4 : ∑ t ∈ Ioc r y, (y / t - c) = ∑ t ∈ Ioc r (y / (c + 1)), (y / t - c) := by
    symm
    apply sum_subset (Ioc_subset_Ioc_right hMy)
    intro t ht ht'
    simp only [mem_Ioc] at ht ht'
    have hlt : y / (c + 1) < t := by omega
    have : y / t < c + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      rw [Nat.div_lt_iff_lt_mul (by omega)] at hlt
      rw [mul_comm]; exact hlt
    omega
  have e5 : ∑ t ∈ Ioc r (y / (c + 1)), (y / t - c) + c * (y / (c + 1) - r)
      = ∑ t ∈ Ioc r (y / (c + 1)), y / t := by
    have hc' : c * (y / (c + 1) - r) = ∑ t ∈ Ioc r (y / (c + 1)), c := by
      rw [sum_const, Nat.card_Ioc, smul_eq_mul, mul_comm]
    rw [hc', ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    have ht' := (mem_Ioc.1 ht).2
    have : c + 1 ≤ y / t := by
      rw [Nat.le_div_iff_mul_le (by have := (mem_Ioc.1 ht).1; omega)]
      rw [Nat.le_div_iff_mul_le (by omega)] at ht'
      rw [mul_comm]; exact ht'
    omega
  rw [e1, e2, sum_congr rfl e3, e4, add_assoc, e5]

/-- When `c < ⌊√y⌋`, `M ≥ ⌊√y⌋`, so the natural subtraction `M - r` is the true difference. -/
lemma sqrt_le_M_of_lt {y c : ℕ} (hc : c < Nat.sqrt y) : Nat.sqrt y ≤ y / (c + 1) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact (Nat.mul_le_mul_left _ hc).trans (Nat.sqrt_le y)

/-- **The incomplete-sum axis swap** (M2d-v report, section 1(b)), for every `y` and every `a`:
with `r = ⌊√y⌋`, `c = min (max (a-1) ⌊y^(1/3)⌋) r`, `M = ⌊y/(c+1)⌋` and floor divisions,
`∑_{a ≤ b ≤ r} ⌊y/b⌋ = ∑_{a ≤ b ≤ c} ⌊y/b⌋ + r (r - c) + ∑_{r < t ≤ M} ⌊y/t⌋ - c (M - r)`,
an identity of integers, where `M - r` is the natural (truncated) difference; by `swap_M_ge` it is
the true difference whenever `c < r`, and when `c = r` both `r (r - c)` and the `t`-sum vanish. -/
theorem axis_swap (y a : ℕ) :
    (∑ b ∈ Icc a (Nat.sqrt y), ((y / b : ℕ) : ℤ))
      = ∑ b ∈ Icc a (sw_c y a), ((y / b : ℕ) : ℤ)
        + (Nat.sqrt y : ℤ) * ((Nat.sqrt y : ℤ) - sw_c y a)
        + ∑ t ∈ Ioc (Nat.sqrt y) (sw_M y a), ((y / t : ℕ) : ℤ)
        - (sw_c y a : ℤ) * ((sw_M y a - Nat.sqrt y : ℕ) : ℤ) := by
  have hcr : sw_c y a ≤ Nat.sqrt y := min_le_right _ _
  have core := swap_core y (sw_c y a) hcr
  have core' : (∑ b ∈ Ioc (sw_c y a) (Nat.sqrt y), ((y / b : ℕ) : ℤ))
      + (sw_c y a : ℤ) * ((sw_M y a - Nat.sqrt y : ℕ) : ℤ)
      = (Nat.sqrt y : ℤ) * ((Nat.sqrt y : ℤ) - sw_c y a)
        + ∑ t ∈ Ioc (Nat.sqrt y) (sw_M y a), ((y / t : ℕ) : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) core
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum] at this
    rw [Nat.cast_sub hcr] at this
    exact this
  -- split `[a, r] = [a, c] ∪ (c, r]`
  have hsplit : ∑ b ∈ Icc a (Nat.sqrt y), ((y / b : ℕ) : ℤ)
      = ∑ b ∈ Icc a (sw_c y a), ((y / b : ℕ) : ℤ)
        + ∑ b ∈ Ioc (sw_c y a) (Nat.sqrt y), ((y / b : ℕ) : ℤ) := by
    by_cases hac : a ≤ sw_c y a + 1
    · rw [← sum_union]
      · congr 1
        ext b; simp only [mem_Icc, mem_union, mem_Ioc]; omega
      · rw [disjoint_left]; intro b h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    · have hc : sw_c y a = Nat.sqrt y := by
        unfold sw_c at hac ⊢
        rcases min_cases (max (a - 1) (icbrt y)) (Nat.sqrt y) with h | h
        · rw [h.1] at hac; have := le_max_left (a - 1) (icbrt y); omega
        · exact h.1
      rw [hc, Ioc_self, sum_empty, add_zero]
  rw [hsplit, ← sw_M] at *
  linarith [core']

theorem swap_M_ge {y a : ℕ} (hc : sw_c y a < Nat.sqrt y) : Nat.sqrt y ≤ sw_M y a :=
  sqrt_le_M_of_lt hc

/-! ## (F1) evaluated with the swap -/

/-- The inner incomplete sum of `B(x)` at row `a`, evaluated by the axis swap with `y = ⌊x/a⌋`. -/
def swapRow (x a : ℕ) : ℤ :=
  ∑ b ∈ Icc a (sw_c (x / a) a), (((x / a) / b : ℕ) : ℤ)
    + (Nat.sqrt (x / a) : ℤ) * ((Nat.sqrt (x / a) : ℤ) - sw_c (x / a) a)
    + ∑ t ∈ Ioc (Nat.sqrt (x / a)) (sw_M (x / a) a), (((x / a) / t : ℕ) : ℤ)
    - (sw_c (x / a) a : ℤ) * ((sw_M (x / a) a - Nat.sqrt (x / a) : ℕ) : ℤ)

/-- `B(x)` with every incomplete row sum replaced by its axis-swapped evaluation. -/
def BsumSwap (x : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 (icbrt x), (swapRow x a - ∑ b ∈ Icc a (ha x a), ((b : ℤ) - 1))

theorem Bsum_eq_BsumSwap (x : ℕ) : Bsum x = BsumSwap x := by
  unfold Bsum BsumSwap
  refine sum_congr rfl fun a _ => ?_
  rw [swapRow, ← axis_swap, ha, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.div_div_eq_div_mul]; ring

/-- **(F1) evaluated with the axis swap equals `D_3`**, for every natural `x`:
`D_3(x) = 6 B_swap(x) - 3 E_ab(x) - 3 E_bc(x) + ⌊x^(1/3)⌋`. -/
theorem D3_eq_F1_swap (x : ℕ) :
    (D3 x : ℤ) = 6 * BsumSwap x - 3 * Eab x - 3 * Ebc x + icbrt x := by
  rw [← Bsum_eq_BsumSwap]; exact ternary_F1 x

end M2L4
