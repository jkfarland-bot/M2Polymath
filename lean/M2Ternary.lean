module

public import Mathlib

/-!
  Seat M2L3, item 1: the ternary count (F1) and the cyclic-orbit identity (M1).
  A19 section 7 (Theorem F) and section 9a (Result M, equation (M1)).
  Every statement is an exact identity for every natural x.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.Moebius

namespace M2L3

/-! ## Integer cube root -/

/-- The integer cube root: the largest `m` with `m ^ 3 ≤ x`. -/
def icbrt (x : ℕ) : ℕ := Nat.findGreatest (fun m => m ^ 3 ≤ x) x

lemma icbrt_pow_le (x : ℕ) : icbrt x ^ 3 ≤ x :=
  Nat.findGreatest_spec (P := fun m => m ^ 3 ≤ x) (m := 0) (Nat.zero_le _) (by simp)

lemma le_of_cube_le {k x : ℕ} (h : k ^ 3 ≤ x) : k ≤ x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ 3 := Nat.pow_le_pow_right hk (by norm_num)
      _ ≤ x := h

lemma le_icbrt {k x : ℕ} (h : k ^ 3 ≤ x) : k ≤ icbrt x :=
  Nat.le_findGreatest (le_of_cube_le h) h

/-- `k ^ 3 ≤ x ↔ k ≤ icbrt x`: the defining property of the integer cube root. -/
lemma cube_le_iff {k x : ℕ} : k ^ 3 ≤ x ↔ k ≤ icbrt x :=
  ⟨le_icbrt, fun h => (Nat.pow_le_pow_left h 3).trans (icbrt_pow_le x)⟩

lemma icbrt_le (x : ℕ) : icbrt x ≤ x := le_of_cube_le (icbrt_pow_le x)

/-- The integer cube root is `floor (x ^ (1/3))` computed in the reals. -/
theorem icbrt_eq_floor (x : ℕ) : icbrt x = ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  symm
  have hx : (0 : ℝ) ≤ x := by positivity
  have key : ∀ k : ℕ, ((k : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) ↔ k ^ 3 ≤ x) := by
    intro k
    rw [← Real.rpow_le_rpow_iff (z := 3) (by positivity) (by positivity) (by norm_num),
      ← Real.rpow_mul hx]
    norm_num
    exact_mod_cast Iff.rfl
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · exact (key _).2 (icbrt_pow_le x)
  · by_contra h
    have h' : (icbrt x : ℝ) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := le_of_not_gt h
    have := le_icbrt ((key (icbrt x + 1)).1 (by exact_mod_cast h'))
    omega

/-! ## The ternary divisor function and its summatory function -/

/-- `d_3 = ζ * ζ * ζ`, the number of ordered factorizations `n = a b c`. -/
def d3 : ArithmeticFunction ℕ := ζ * ζ * ζ

/-- `D_3(x) = ∑_{1 ≤ n ≤ x} d_3(n)`. -/
def D3 (x : ℕ) : ℕ := ∑ n ∈ Ioc 0 x, d3 n

lemma d3_eq_sigma0_mul_zeta : d3 = σ 0 * ζ := by
  rw [d3, ← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

lemma D3_eq_double (x : ℕ) : D3 x = ∑ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, x / (a * b) := by
  unfold D3 d3
  rw [mul_assoc, sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun a ha => ?_
  have ha' : 0 < a := (mem_Ioc.1 ha).1
  have hz := sum_Ioc_mul_zeta_eq_sum (ζ : ArithmeticFunction ℕ) (x / a)
  simp only [natCoe_nat, Nat.cast_id] at hz
  rw [zeta_apply, ite_eq_right (by omega), one_mul, hz]
  have h1 : ∑ b ∈ Ioc 0 (x / a), ζ b * (x / a / b) = ∑ b ∈ Ioc 0 (x / a), x / (a * b) := by
    refine sum_congr rfl fun b hb => ?_
    have hb' : 0 < b := (mem_Ioc.1 hb).1
    rw [zeta_apply, ite_eq_right (by omega), one_mul, Nat.div_div_eq_div_mul]
  rw [h1]
  apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self _ _))
  intro b hb hnb
  simp only [mem_Ioc, not_and, not_le] at hb hnb
  apply Nat.div_eq_of_lt
  have := hnb hb.1
  rw [Nat.div_lt_iff_lt_mul ha'] at this
  linarith [mul_comm a b]

/-! ## Box sums over `(0, x]^3` -/

/-- The symmetric weight `[a b c ≤ x]`. -/
def phi (x a b c : ℕ) : ℤ := if a * b * c ≤ x then 1 else 0

lemma phi_perm1 (x a b c : ℕ) : phi x a b c = phi x a c b := by
  unfold phi; rw [show a * b * c = a * c * b by ring]
lemma phi_perm2 (x a b c : ℕ) : phi x a b c = phi x b a c := by
  unfold phi; rw [show a * b * c = b * a * c by ring]
lemma phi_perm3 (x a b c : ℕ) : phi x a b c = phi x b c a := by
  unfold phi; rw [show a * b * c = b * c * a by ring]
lemma phi_perm4 (x a b c : ℕ) : phi x a b c = phi x c a b := by
  unfold phi; rw [show a * b * c = c * a * b by ring]
lemma phi_perm5 (x a b c : ℕ) : phi x a b c = phi x c b a := by
  unfold phi; rw [show a * b * c = c * b * a by ring]

lemma ind_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℤ) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- Counting a set of `c` in `(0, x]` that is an integer interval `[lo, hi]`. -/
lemma count_interval (x lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ c, (c ∈ Ioc 0 x ∧ P c) ↔ (lo ≤ c ∧ c ≤ hi)) :
    ∑ c ∈ Ioc 0 x, (if P c then (1 : ℤ) else 0) = ((hi + 1 - lo : ℕ) : ℤ) := by
  rw [sum_boole]
  congr 1
  have : (Ioc 0 x).filter P = Icc lo hi := by
    ext c; rw [mem_filter, mem_Icc]; exact hP c
  rw [this, Nat.card_Icc]

lemma sum_phi (x : ℕ) : (D3 x : ℤ) = ∑ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x, phi x a b c := by
  rw [D3_eq_double]; push_cast
  refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
  have ha' : 0 < a := (mem_Ioc.1 ha).1
  have hb' : 0 < b := (mem_Ioc.1 hb).1
  unfold phi
  rw [count_interval x 1 (x / (a * b))]
  · push_cast; ring
  · intro c
    rw [mem_Ioc, Nat.le_div_iff_mul_le (by positivity)]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by linarith [mul_comm (a * b) c]⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, by linarith [mul_comm (a * b) c]⟩
      have : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
      nlinarith

/-! ## Relabelling the three summation variables -/

section Relabel
variable (X : Finset ℕ) (F : ℕ → ℕ → ℕ → ℤ)

lemma rl_acb : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F a c b = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F a b c :=
  sum_congr rfl fun _ _ => sum_comm
lemma rl_bac : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F b a c = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F a b c :=
  sum_comm
lemma rl_bca : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F b c a = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F a b c := by
  rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_comm
lemma rl_cab : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F c a b = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F a b c :=
  (rl_bca X (fun a b c => F c a b)).symm
lemma rl_cba : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F c b a = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, F a b c :=
  (rl_bca X (fun a b c => F b a c)).trans (rl_bac X F)

end Relabel

/-! ## The sorted-triple weights -/

/-- The weight `2 [a ≤ b ≤ c] - [a = b ≤ c] - [a ≤ b = c]`. -/
def gw (a b c : ℕ) : ℤ :=
  2 * (if a ≤ b ∧ b ≤ c then 1 else 0) - (if a = b ∧ b ≤ c then 1 else 0)
    - (if a ≤ b ∧ b = c then 1 else 0)

/-- The diagonal weight `[a = b = c]`. -/
def dw (a b c : ℕ) : ℤ := if a = b ∧ b = c then 1 else 0

/-- Pointwise: the six permuted copies of `gw` plus `2 dw` always sum to 2. -/
lemma gw_pointwise (a b c : ℕ) :
    gw a b c + gw a c b + gw b a c + gw b c a + gw c a b + gw c b a + 2 * dw a b c = 2 := by
  unfold gw dw
  rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy b c with h2 | h2 | h2 <;>
    rcases lt_trichotomy a c with h3 | h3 | h3 <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> omega

/-- The cyclic-orbit predicate of (M1): `a ≤ b` and `a < c`. -/
def rw3 (a b c : ℕ) : ℤ := if a ≤ b ∧ a < c then 1 else 0

lemma rw3_pointwise (a b c : ℕ) : dw a b c + rw3 a b c + rw3 b c a + rw3 c a b = 1 := by
  unfold dw rw3
  rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy b c with h2 | h2 | h2 <;>
    rcases lt_trichotomy a c with h3 | h3 | h3 <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> omega

/-! ## (F1): the symmetric-triple formula -/

/-- `m = floor (x ^ (1/3))` and `h_a = floor (sqrt (floor (x / a)))`. -/
def ha (x a : ℕ) : ℕ := Nat.sqrt (x / a)

/-- `B(x) = ∑_{a=1}^{m} ∑_{b=a}^{h_a} (floor (x / (a b)) - b + 1)`. -/
def Bsum (x : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 (icbrt x), ∑ b ∈ Icc a (ha x a), (((x / (a * b) : ℕ) : ℤ) - b + 1)

/-- `E_ab(x) = ∑_{a=1}^{m} (floor (x / a^2) - a + 1)`. -/
def Eab (x : ℕ) : ℤ := ∑ a ∈ Icc 1 (icbrt x), (((x / a ^ 2 : ℕ) : ℤ) - a + 1)

/-- `E_bc(x) = ∑_{a=1}^{m} (h_a - a + 1)`. -/
def Ebc (x : ℕ) : ℤ := ∑ a ∈ Icc 1 (icbrt x), ((ha x a : ℤ) - a + 1)

lemma le_ha_iff {x a b : ℕ} (ha0 : 0 < a) : b ≤ ha x a ↔ a * b * b ≤ x := by
  rw [ha, Nat.le_sqrt, Nat.le_div_iff_mul_le ha0]
  constructor <;> intro h <;> linarith [mul_comm (b * b) a, mul_assoc a b b]

lemma a_le_ha_iff {x a : ℕ} (ha0 : 0 < a) : a ≤ ha x a ↔ a ≤ icbrt x := by
  rw [le_ha_iff ha0, ← cube_le_iff]; ring_nf

/-- Restrict a sum over `(0, x]` to `[1, icbrt x]` when the summand vanishes above `icbrt x`. -/
lemma restrict_icbrt (x : ℕ) (f : ℕ → ℤ) (hf : ∀ a, 0 < a → icbrt x < a → f a = 0) :
    ∑ a ∈ Ioc 0 x, f a = ∑ a ∈ Icc 1 (icbrt x), f a := by
  symm
  apply sum_subset
  · intro a h; rw [mem_Icc] at h; rw [mem_Ioc]; exact ⟨h.1, h.2.trans (icbrt_le x)⟩
  · intro a h1 h2
    rw [mem_Ioc] at h1; rw [mem_Icc] at h2
    exact hf a h1.1 (by omega)

lemma T_eq (x : ℕ) :
    ∑ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x,
      (if a ≤ b ∧ b ≤ c then (1 : ℤ) else 0) * phi x a b c = Bsum x := by
  unfold Bsum phi
  simp only [ind_mul]
  have inner : ∀ a ∈ Ioc 0 x, ∀ b ∈ Ioc 0 x,
      ∑ c ∈ Ioc 0 x, (if (a ≤ b ∧ b ≤ c) ∧ a * b * c ≤ x then (1 : ℤ) else 0)
        = if a ≤ b ∧ b ≤ ha x a then ((x / (a * b) : ℕ) : ℤ) - b + 1 else 0 := by
    intro a ha' b hb'
    have ha0 : 0 < a := (mem_Ioc.1 ha').1
    have hb0 : 0 < b := (mem_Ioc.1 hb').1
    have hab : 0 < a * b := by positivity
    split_ifs with h
    · have hb1 : a * b * b ≤ x := (le_ha_iff ha0).1 h.2
      have hb2 : b ≤ x / (a * b) := (Nat.le_div_iff_mul_le hab).2 (by linarith [mul_comm b (a * b)])
      rw [count_interval x b (x / (a * b))]
      · push_cast [show b ≤ x / (a * b) + 1 by omega]; ring
      · intro c
        rw [mem_Ioc, Nat.le_div_iff_mul_le hab]
        constructor
        · rintro ⟨_, ⟨_, h2⟩, h3⟩; exact ⟨h2, by linarith [mul_comm (a * b) c]⟩
        · rintro ⟨h1, h3⟩
          refine ⟨⟨by omega, ?_⟩, ⟨h.1, h1⟩, by linarith [mul_comm (a * b) c]⟩
          nlinarith
    · apply sum_eq_zero
      intro c _
      rw [ite_eq_right]
      rintro ⟨⟨h1, h2⟩, h3⟩
      apply h ⟨h1, (le_ha_iff ha0).2 ?_⟩
      calc a * b * b ≤ a * b * c := Nat.mul_le_mul_left _ h2
        _ ≤ x := h3
  rw [sum_congr rfl fun a ha' => sum_congr rfl fun b hb' => inner a ha' b hb']
  have mid : ∀ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x,
      (if a ≤ b ∧ b ≤ ha x a then ((x / (a * b) : ℕ) : ℤ) - b + 1 else 0)
        = ∑ b ∈ Icc a (ha x a), (((x / (a * b) : ℕ) : ℤ) - b + 1) := by
    intro a ha'
    have ha0 : 0 < a := (mem_Ioc.1 ha').1
    rw [← sum_filter]
    congr 1
    ext b
    rw [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by omega, ?_⟩, h1, h2⟩
      have h3 := (le_ha_iff ha0).1 h2
      have h4 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      calc b = 1 * b := (one_mul b).symm
        _ ≤ a * b * b := Nat.mul_le_mul_right b h4
        _ ≤ x := h3
  rw [sum_congr rfl mid]
  apply restrict_icbrt
  intro a ha0 hlt
  apply sum_eq_zero
  intro b hb
  exfalso
  rw [mem_Icc] at hb
  have := (a_le_ha_iff (x := x) ha0).1 (hb.1.trans hb.2)
  omega

lemma restrict_icbrt_ite (x : ℕ) (f : ℕ → ℤ) :
    ∑ a ∈ Ioc 0 x, (if a ≤ icbrt x then f a else 0) = ∑ a ∈ Icc 1 (icbrt x), f a := by
  rw [restrict_icbrt x _ (fun a _ h => ite_eq_right (by omega))]
  exact sum_congr rfl fun a h => ite_eq_left (mem_Icc.1 h).2

/-- Collapse a sum over `b` against the condition `a = b`. -/
lemma collapse_eq (X : Finset ℕ) (a : ℕ) (ha : a ∈ X) (G : ℕ → ℕ → ℤ) (P : ℕ → ℕ → Prop)
    [∀ b c, Decidable (P b c)] :
    ∑ b ∈ X, ∑ c ∈ X, (if a = b ∧ P b c then G b c else 0) = ∑ c ∈ X, (if P a c then G a c else 0) := by
  trans ∑ b ∈ X, (if a = b then ∑ c ∈ X, (if P a c then G a c else 0) else 0)
  · refine sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · subst hab; exact sum_congr rfl fun c _ => by simp only [true_and]
    · exact sum_eq_zero fun c _ => ite_eq_right (fun h => hab h.1)
  · rw [sum_ite_eq, ite_eq_left ha]

lemma Eab_eq (x : ℕ) :
    ∑ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x,
      (if a = b ∧ b ≤ c then (1 : ℤ) else 0) * phi x a b c = Eab x := by
  unfold Eab phi
  simp only [ind_mul, and_assoc]
  rw [sum_congr rfl fun a ha' => collapse_eq (Ioc 0 x) a ha' (fun _ _ => 1)
    (fun b c => b ≤ c ∧ a * b * c ≤ x)]
  rw [← restrict_icbrt_ite]
  refine sum_congr rfl fun a ha' => ?_
  have ha0 : 0 < a := (mem_Ioc.1 ha').1
  have ha2 : 0 < a * a := by positivity
  split_ifs with hm
  · have h3 : a * a * a ≤ x := by have := cube_le_iff.2 hm; ring_nf; ring_nf at this; exact this
    have hb2 : a ≤ x / a ^ 2 := by
      rw [Nat.le_div_iff_mul_le (by positivity)]; ring_nf; ring_nf at h3; exact h3
    rw [count_interval x a (x / a ^ 2)]
    · push_cast [show a ≤ x / a ^ 2 + 1 by omega]; ring
    · intro c
      rw [mem_Ioc, Nat.le_div_iff_mul_le (by positivity)]
      constructor
      · rintro ⟨_, h2, h3⟩; exact ⟨h2, by linarith [mul_comm (a ^ 2) c, sq a]⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨by omega, ?_⟩, h1, by nlinarith [mul_comm (a ^ 2) c, sq a]⟩
        nlinarith
  · apply sum_eq_zero
    intro c _
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    apply hm
    rw [← cube_le_iff]
    calc a ^ 3 = a * a * a := by ring
      _ ≤ a * a * c := Nat.mul_le_mul_left _ h1
      _ ≤ x := h2

lemma Ebc_eq (x : ℕ) :
    ∑ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x,
      (if a ≤ b ∧ b = c then (1 : ℤ) else 0) * phi x a b c = Ebc x := by
  unfold Ebc phi
  simp only [ind_mul]
  have step : ∀ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x,
      (if (a ≤ b ∧ b = c) ∧ a * b * c ≤ x then (1 : ℤ) else 0)
        = ∑ b ∈ Ioc 0 x, (if a ≤ b ∧ a * b * b ≤ x then (1 : ℤ) else 0) := by
    intro a _
    refine sum_congr rfl fun b hb => ?_
    rw [sum_eq_single_of_mem b hb (fun c _ hcb => ite_eq_right (fun h => hcb h.1.2.symm))]
    simp
  rw [sum_congr rfl step, ← restrict_icbrt_ite]
  refine sum_congr rfl fun a ha' => ?_
  have ha0 : 0 < a := (mem_Ioc.1 ha').1
  split_ifs with hm
  · have hle : a ≤ ha x a := (a_le_ha_iff ha0).2 hm
    rw [count_interval x a (ha x a)]
    · push_cast [show a ≤ ha x a + 1 by omega]; ring
    · intro b
      rw [mem_Ioc, le_ha_iff ha0]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩
        refine ⟨⟨by omega, ?_⟩, h1, h2⟩
        have h4 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
        calc b = 1 * b := (one_mul b).symm
          _ ≤ a * b * b := Nat.mul_le_mul_right b h4
          _ ≤ x := h2
  · apply sum_eq_zero
    intro b _
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hm ((a_le_ha_iff ha0).1 (h1.trans ((le_ha_iff ha0).2 h2)))

lemma diag_eq (x : ℕ) :
    ∑ a ∈ Ioc 0 x, ∑ b ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x, dw a b c * phi x a b c = icbrt x := by
  unfold dw phi
  simp only [ind_mul, and_assoc]
  rw [sum_congr rfl fun a ha' => collapse_eq (Ioc 0 x) a ha' (fun _ _ => 1)
    (fun b c => b = c ∧ a * b * c ≤ x)]
  have step : ∀ a ∈ Ioc 0 x, ∑ c ∈ Ioc 0 x, (if a = c ∧ a * a * c ≤ x then (1 : ℤ) else 0)
      = if a ≤ icbrt x then 1 else 0 := by
    intro a ha'
    rw [sum_eq_single_of_mem a ha' (fun c _ hca => ite_eq_right (fun h => hca h.1.symm))]
    have : a * a * a ≤ x ↔ a ≤ icbrt x := by rw [← cube_le_iff]; ring_nf
    simp only [true_and, this]
  rw [sum_congr rfl step]
  exact (restrict_icbrt_ite x (fun _ => 1)).trans (by simp)

/-! ## Main theorem (F1) -/

section Main
variable (x : ℕ)

local notation "X" => Ioc 0 x

/-- `W = ∑ gw · phi` over the box. -/
def Wsum : ℤ := ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, gw a b c * phi x a b c

lemma W_acb : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, gw a c b * phi x a b c = Wsum x :=
  (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
    rw [phi_perm1 x a b c]).trans (rl_acb X (fun a b c => gw a b c * phi x a b c))
lemma W_bac : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, gw b a c * phi x a b c = Wsum x :=
  (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
    rw [phi_perm2 x a b c]).trans (rl_bac X (fun a b c => gw a b c * phi x a b c))
lemma W_bca : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, gw b c a * phi x a b c = Wsum x :=
  (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
    rw [phi_perm3 x a b c]).trans (rl_bca X (fun a b c => gw a b c * phi x a b c))
lemma W_cab : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, gw c a b * phi x a b c = Wsum x :=
  (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
    rw [phi_perm4 x a b c]).trans (rl_cab X (fun a b c => gw a b c * phi x a b c))
lemma W_cba : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, gw c b a * phi x a b c = Wsum x :=
  (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
    rw [phi_perm5 x a b c]).trans (rl_cba X (fun a b c => gw a b c * phi x a b c))

lemma W_eq : Wsum x = 2 * Bsum x - Eab x - Ebc x := by
  rw [← T_eq, ← Eab_eq, ← Ebc_eq, Wsum]
  simp only [gw, sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]

/-- **(F1)**, A19 section 7: for every natural `x`,
`D_3(x) = 6 B(x) - 3 E_ab(x) - 3 E_bc(x) + m` with `m = floor (x^(1/3))`,
`h_a = floor (sqrt (floor (x/a)))`, `B(x) = ∑_{a=1}^{m} ∑_{b=a}^{h_a} (floor (x/(ab)) - b + 1)`,
`E_ab(x) = ∑_{a=1}^{m} (floor (x/a^2) - a + 1)`, `E_bc(x) = ∑_{a=1}^{m} (h_a - a + 1)`. -/
theorem ternary_F1 : (D3 x : ℤ) = 6 * Bsum x - 3 * Eab x - 3 * Ebc x + icbrt x := by
  have h2 : 2 * (D3 x : ℤ) = 6 * Wsum x + 2 * (icbrt x : ℤ) := by
    rw [sum_phi, mul_sum]
    have : ∀ a b c, 2 * phi x a b c = gw a b c * phi x a b c + gw a c b * phi x a b c
        + gw b a c * phi x a b c + gw b c a * phi x a b c + gw c a b * phi x a b c
        + gw c b a * phi x a b c + 2 * (dw a b c * phi x a b c) := by
      intro a b c
      rw [← mul_assoc, ← add_mul, ← add_mul, ← add_mul, ← add_mul, ← add_mul, ← add_mul,
        gw_pointwise]
    simp only [mul_sum, this, sum_add_distrib]
    simp only [← mul_sum]
    rw [diag_eq, W_acb, W_bac, W_bca, W_cab, W_cba, Wsum]
    ring
  rw [W_eq] at h2
  linarith

/-- The same statement with `m` written as the real floor `floor (x ^ (1/3))`. -/
theorem ternary_F1_real :
    (D3 x : ℤ) = 6 * Bsum x - 3 * Eab x - 3 * Ebc x + ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  rw [← icbrt_eq_floor]; exact ternary_F1 x

/-! ## (M1): `D_3(x) = floor (x^(1/3)) + 3 H(x)` -/

/-- The triples counted by `H`: positive `(a, b, c)` with `a b c ≤ x`, `a ≤ b`, `a < c`. -/
def Hset : Finset (ℕ × ℕ × ℕ) :=
  (X ×ˢ X ×ˢ X).filter (fun t => t.1 * t.2.1 * t.2.2 ≤ x ∧ t.1 ≤ t.2.1 ∧ t.1 < t.2.2)

/-- `H(x) = #{(a, b, c) ∈ ℕ_{>0}^3 : a b c ≤ x, a ≤ b, a < c}`. -/
def H : ℕ := (Hset x).card

/-- Membership in `Hset` is exactly the defining condition (the box bound is automatic). -/
lemma mem_Hset (a b c : ℕ) :
    (a, b, c) ∈ Hset x ↔ 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c ≤ x ∧ a ≤ b ∧ a < c := by
  simp only [Hset, mem_filter, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩, ⟨h3, _⟩⟩, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hbc : 1 ≤ b * c := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hac : 1 ≤ a * c := Nat.one_le_iff_ne_zero.2 (by positivity)
    refine ⟨⟨⟨h1, ?_⟩, ⟨h2, ?_⟩, ⟨h3, ?_⟩⟩, h4, h5, h6⟩
    · calc a = a * 1 := (mul_one a).symm
        _ ≤ a * (b * c) := Nat.mul_le_mul_left a hbc
        _ = a * b * c := (mul_assoc a b c).symm
        _ ≤ x := h4
    · calc b = 1 * b * 1 := by ring
        _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul_right b (by omega)) (by omega)
        _ ≤ x := h4
    · calc c = 1 * c := (one_mul c).symm
        _ ≤ a * b * c := Nat.mul_le_mul_right c hab
        _ ≤ x := h4

lemma H_eq_sum : (H x : ℤ) = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, rw3 a b c * phi x a b c := by
  rw [H, Hset, card_filter]
  push_cast
  rw [sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_product]
  refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  unfold rw3 phi
  rw [ind_mul]
  congr 1
  exact propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- **(M1)**, A19 section 9a: for every natural `x`, as an exact integer equality,
`D_3(x) = floor (x^(1/3)) + 3 H(x)`. -/
theorem ternary_M1 : D3 x = icbrt x + 3 * H x := by
  have key : (D3 x : ℤ) = icbrt x + 3 * H x := by
    rw [sum_phi, H_eq_sum, ← diag_eq x]
    have : ∀ a b c, phi x a b c = dw a b c * phi x a b c + rw3 a b c * phi x a b c
        + rw3 b c a * phi x a b c + rw3 c a b * phi x a b c := by
      intro a b c
      rw [← add_mul, ← add_mul, ← add_mul, rw3_pointwise, one_mul]
    have e1 : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, rw3 b c a * phi x a b c
        = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, rw3 a b c * phi x a b c :=
      (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
        rw [phi_perm3 x a b c]).trans (rl_bca X (fun a b c => rw3 a b c * phi x a b c))
    have e2 : ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, rw3 c a b * phi x a b c
        = ∑ a ∈ X, ∑ b ∈ X, ∑ c ∈ X, rw3 a b c * phi x a b c :=
      (sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by
        rw [phi_perm4 x a b c]).trans (rl_cab X (fun a b c => rw3 a b c * phi x a b c))
    rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => this a b c]
    simp only [sum_add_distrib]
    rw [e1, e2]
    ring
  exact_mod_cast key

/-- `D_3(x) ≡ floor (x^(1/3)) (mod 3)`. -/
theorem D3_mod3 : D3 x % 3 = icbrt x % 3 := by
  rw [ternary_M1]; omega

end Main

end M2L3
