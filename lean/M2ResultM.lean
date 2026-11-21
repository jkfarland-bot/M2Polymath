module

public import Mathlib
public import M2Polymath

/-!
  Seat M2L4, item 1: the rest of Result M (A19 section 9a).
  Second transform of (M2), the recovery of H from D_3 mod 9, the exact identities (M3) and (M4),
  and the two oracle reductions as Lean functions proved correct, for every natural x.
  Builds on round 3 (M2Ternary: (M1); M2Polymath: (F2), S_3 mod 9, first transform of (M2) for x >= 1).
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace M2L4
open M2L3

/-! ## Integer k-th roots -/

/-- The integer `k`-th root: the largest `m ≤ x` with `m ^ k ≤ x`. -/
def iroot (k x : ℕ) : ℕ := Nat.findGreatest (fun m => m ^ k ≤ x) x

lemma iroot_pow_le {k : ℕ} (hk : 0 < k) (x : ℕ) : iroot k x ^ k ≤ x :=
  Nat.findGreatest_spec (P := fun m => m ^ k ≤ x) (m := 0) (Nat.zero_le _)
    (by simp [Nat.zero_pow hk])

lemma le_of_pow_le' {k m x : ℕ} (hk : 0 < k) (h : m ^ k ≤ x) : m ≤ x :=
  (Nat.le_self_pow hk.ne' m).trans h

/-- `m ^ k ≤ x ↔ m ≤ iroot k x` for `k ≥ 1`. -/
lemma pow_le_iff_le_iroot {k m x : ℕ} (hk : 0 < k) : m ^ k ≤ x ↔ m ≤ iroot k x :=
  ⟨fun h => Nat.le_findGreatest (le_of_pow_le' hk h) h,
   fun h => (Nat.pow_le_pow_left h k).trans (iroot_pow_le hk x)⟩

lemma iroot_le {k : ℕ} (hk : 0 < k) (x : ℕ) : iroot k x ≤ x :=
  le_of_pow_le' hk (iroot_pow_le hk x)

lemma icbrt_eq_iroot (x : ℕ) : icbrt x = iroot 3 x := rfl

lemma iroot_one (x : ℕ) : iroot 1 x = x := by
  apply le_antisymm (iroot_le one_pos x)
  exact (pow_le_iff_le_iroot one_pos).1 (by simp)

/-- The floor-root query arguments: `iroot k x = ⌊x ^ (1/k)⌋` computed in the reals. -/
theorem iroot_eq_floor {k : ℕ} (hk : 0 < k) (x : ℕ) :
    iroot k x = ⌊(x : ℝ) ^ ((1 : ℝ) / k)⌋₊ := by
  symm
  have hx : (0 : ℝ) ≤ x := by positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have key : ∀ m : ℕ, ((m : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / k) ↔ m ^ k ≤ x) := by
    intro m
    rw [← Real.rpow_le_rpow_iff (z := (k : ℝ)) (by positivity) (by positivity) hk',
      ← Real.rpow_mul hx, one_div_mul_cancel hk'.ne', Real.rpow_one, Real.rpow_natCast]
    exact_mod_cast Iff.rfl
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · exact (key _).2 (iroot_pow_le hk x)
  · by_contra h
    have h' : (iroot k x : ℝ) + 1 ≤ (x : ℝ) ^ ((1 : ℝ) / k) := le_of_not_gt h
    have := (pow_le_iff_le_iroot hk).1 ((key (iroot k x + 1)).1 (by exact_mod_cast h'))
    omega

/-- Nested roots: `iroot e (iroot j x) = iroot (e j) x`. -/
lemma iroot_iroot {e j : ℕ} (he : 0 < e) (hj : 0 < j) (x : ℕ) :
    iroot e (iroot j x) = iroot (e * j) x := by
  apply eq_of_forall_le_iff
  intro m
  rw [← pow_le_iff_le_iroot he, ← pow_le_iff_le_iroot hj, ← pow_le_iff_le_iroot (by positivity),
    pow_mul]

/-! ## Prime counts at roots -/

/-- `P k x = #{p prime : p ^ k ≤ x}` (the set used in round 3). -/
def P (k x : ℕ) : ℕ := ((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card

lemma P_eq_primeCounting {k : ℕ} (hk : 0 < k) (x : ℕ) : P k x = Nat.primeCounting (iroot k x) := by
  rw [← prime_count_one]
  unfold P
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, pow_one]
  constructor
  · rintro ⟨⟨h0, _⟩, hp, h⟩
    have := (pow_le_iff_le_iroot hk).1 h
    exact ⟨⟨h0, this⟩, hp, this⟩
  · rintro ⟨⟨h0, h1⟩, hp, _⟩
    have := (pow_le_iff_le_iroot hk).2 h1
    exact ⟨⟨h0, le_of_pow_le' hk this⟩, hp, this⟩

lemma P_iroot {e j : ℕ} (he : 0 < e) (hj : 0 < j) (x : ℕ) : P e (iroot j x) = P (e * j) x := by
  rw [P_eq_primeCounting he, P_eq_primeCounting (by positivity), iroot_iroot he hj]

lemma P_eq_zero {k x : ℕ} (h : x < 2 ^ k) : P k x = 0 := by
  unfold P
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro p - ⟨hp, hpk⟩
  have := Nat.pow_le_pow_left hp.two_le k
  omega

lemma sum_Ioc_trim {m A : ℕ} (g : ℕ → ℤ) (hA : m ≤ A) (hg : ∀ k, m < k → g k = 0) :
    ∑ k ∈ Ioc 0 A, g k = ∑ k ∈ Ioc 0 m, g k := by
  symm
  apply sum_subset (Ioc_subset_Ioc_right hA)
  intro k hk hk'
  simp only [mem_Ioc] at hk hk'
  exact hg k (by omega)

/-- `G(x) = ∑_{1 ≤ e ≤ N} e · #{q prime : q^e ≤ x}` for any `N` with `x < 2^(N+1)`. -/
theorem Gpp_eq_sum_trim {x N : ℕ} (hN : x < 2 ^ (N + 1)) :
    Gpp x = ∑ k ∈ Ioc 0 N, (k : ℤ) * P k x := by
  have hz : ∀ k, min x N < k → (k : ℤ) * P k x = 0 := by
    intro k hk
    rw [P_eq_zero, Nat.cast_zero, mul_zero]
    rcases min_lt_iff.1 hk with h | h
    · exact lt_of_le_of_lt (Nat.lt_two_pow_self).le (Nat.pow_lt_pow_right (by norm_num) h)
    · exact lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) h)
  rw [Gpp_eq_sum_prime_counts]
  change ∑ k ∈ Ioc 0 x, (k : ℤ) * (P k x : ℤ) = _
  rw [sum_Ioc_trim _ (min_le_left x N) hz,
    sum_Ioc_trim _ (min_le_right x N) hz]

lemma lt_two_pow_log (x : ℕ) : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x

lemma Icc_one_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext k; simp only [mem_Icc, mem_Ioc]; omega

/-- **(M4)**, the second sum written with prime counts at roots:
`G(x) = ∑_{1 ≤ e ≤ ⌊log₂ x⌋} e · π(⌊x^(1/e)⌋)`, exact, for every `x`. -/
theorem Gpp_eq_sum_primeCounting (x : ℕ) :
    Gpp x = ∑ e ∈ Icc 1 (Nat.log 2 x), (e : ℤ) * Nat.primeCounting (iroot e x) := by
  rw [Gpp_eq_sum_trim (lt_two_pow_log x), Icc_one_eq_Ioc]
  refine sum_congr rfl fun e he => ?_
  rw [P_eq_primeCounting (mem_Ioc.1 he).1]

/-- **(M3)**, exact over the integers for every `x`:
`π(x) = G(x) - ∑_{2 ≤ e ≤ ⌊log₂ x⌋} e · π(⌊x^(1/e)⌋)`. In particular the mod 3 form holds. -/
theorem primeCounting_M3 (x : ℕ) :
    (Nat.primeCounting x : ℤ)
      = Gpp x - ∑ e ∈ Icc 2 (Nat.log 2 x), (e : ℤ) * Nat.primeCounting (iroot e x) := by
  rw [Gpp_eq_sum_primeCounting]
  rcases Nat.eq_zero_or_pos (Nat.log 2 x) with h0 | hpos
  · rw [h0]
    have hx : x < 2 := by simpa [h0] using lt_two_pow_log x
    interval_cases x <;> simp
  · have hs : Icc 1 (Nat.log 2 x) = insert 1 (Icc 2 (Nat.log 2 x)) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hs, sum_insert (by simp), iroot_one]
    ring

/-! ## Hyperbola regrouping and Möbius inversion -/

lemma sum_hyperbola_eq (F : ℕ → ℕ → ℤ) (N : ℕ) :
    ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), F a b
      = ∑ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, F x.1 x.2 := by
  trans ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, F x.1 x.2
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun a ha => ?_
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext b
    simp only [mem_filter, mem_Ioc] at ha ⊢
    rw [Nat.le_div_iff_mul_le ha.1]
    constructor
    · rintro ⟨hb, h⟩
      refine ⟨⟨hb, ?_⟩, by rw [mul_comm]; exact h⟩
      exact (Nat.le_mul_of_pos_right b ha.1).trans h
    · rintro ⟨⟨hb, _⟩, h⟩
      exact ⟨hb, by rw [mul_comm]; exact h⟩
  · trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, F x.1 x.2
    · simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun x hx => ?_
      simp only [mem_product, mem_Ioc] at hx
      rw [sum_ite_eq]
      simp only [mem_Ioc]
      have : 0 < x.1 * x.2 := Nat.mul_pos hx.1.1 hx.2.1
      by_cases h : x.1 * x.2 ≤ N <;> simp [h, this]
    · refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]

/-- Möbius inversion over the hyperbola, `μ` on the inner variable. -/
lemma sum_hyperbola_moebius_inner (f : ℕ → ℤ) (N : ℕ) :
    ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), (μ b : ℤ) * f (a * b) = if 1 ≤ N then f 1 else 0 := by
  rw [sum_hyperbola_eq (fun a b => (μ b : ℤ) * f (a * b))]
  have : ∀ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, (μ x.2 : ℤ) * f (x.1 * x.2)
      = if n = 1 then f 1 else 0 := by
    intro n _
    have h1 : ∀ x ∈ n.divisorsAntidiagonal, (μ x.2 : ℤ) * f (x.1 * x.2)
        = f n * ((ζ : ArithmeticFunction ℤ) x.1 * (μ : ArithmeticFunction ℤ) x.2) := by
      intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      have hx1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hx; exact hx.2 hx.1.symm
      rw [hx.1, natCoe_apply, zeta_apply, ite_eq_right hx1]
      push_cast; ring
    rw [sum_congr rfl h1, ← mul_sum, ← mul_apply, coe_zeta_mul_moebius, one_apply]
    split_ifs with h <;> simp [h]
  rw [sum_congr rfl this, sum_ite_eq']
  simp [mem_Ioc]

/-- Möbius inversion over the hyperbola, `μ` on the outer variable. -/
lemma sum_hyperbola_moebius_outer (f : ℕ → ℤ) (N : ℕ) :
    ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), (μ a : ℤ) * f (a * b) = if 1 ≤ N then f 1 else 0 := by
  rw [sum_hyperbola_eq (fun a b => (μ a : ℤ) * f (a * b))]
  have : ∀ n ∈ Ioc 0 N, ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * f (x.1 * x.2)
      = if n = 1 then f 1 else 0 := by
    intro n _
    have h1 : ∀ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℤ) * f (x.1 * x.2)
        = f n * ((μ : ArithmeticFunction ℤ) x.1 * (ζ : ArithmeticFunction ℤ) x.2) := by
      intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      have hx2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hx; exact hx.2 hx.1.symm
      rw [hx.1, natCoe_apply, zeta_apply, ite_eq_right hx2]
      push_cast; ring
    rw [sum_congr rfl h1, ← mul_sum, ← mul_apply, moebius_mul_coe_zeta, one_apply]
    split_ifs with h <;> simp [h]
  rw [sum_congr rfl this, sum_ite_eq']
  simp [mem_Ioc]

/-- **(M4)**, exact for every `x`: `π(x) = ∑_{1 ≤ j ≤ ⌊log₂ x⌋} μ(j) j G(⌊x^(1/j)⌋)`. -/
theorem primeCounting_M4 (x : ℕ) :
    (Nat.primeCounting x : ℤ)
      = ∑ j ∈ Icc 1 (Nat.log 2 x), (μ j : ℤ) * j * Gpp (iroot j x) := by
  set N := Nat.log 2 x with hNdef
  have hN : x < 2 ^ (N + 1) := lt_two_pow_log x
  -- each `G(⌊x^(1/j)⌋)` trimmed to `e ≤ N / j`
  have hG : ∀ j ∈ Ioc 0 N, Gpp (iroot j x) = ∑ e ∈ Ioc 0 (N / j), (e : ℤ) * P (j * e) x := by
    intro j hj
    have hj0 : 0 < j := (mem_Ioc.1 hj).1
    have hb : iroot j x < 2 ^ (N / j + 1) := by
      by_contra hc
      push Not at hc
      have h1 := Nat.pow_le_pow_left hc j
      rw [← pow_mul] at h1
      have h2 : N + 1 ≤ (N / j + 1) * j := by
        have := Nat.lt_div_mul_add hj0 (a := N); rw [add_mul, one_mul]; omega
      have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
      have h4 := iroot_pow_le hj0 x
      omega
    rw [Gpp_eq_sum_trim hb]
    refine sum_congr rfl fun e he => ?_
    rw [P_iroot (mem_Ioc.1 he).1 hj0, mul_comm e j]
  rw [Icc_one_eq_Ioc]
  have hR : ∑ j ∈ Ioc 0 N, (μ j : ℤ) * j * Gpp (iroot j x)
      = ∑ j ∈ Ioc 0 N, ∑ e ∈ Ioc 0 (N / j), (μ j : ℤ) * (((j * e : ℕ) : ℤ) * P (j * e) x) := by
    refine sum_congr rfl fun j hj => ?_
    rw [hG j hj, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    push_cast; ring
  rw [hR, sum_hyperbola_moebius_outer (fun r => ((r : ℕ) : ℤ) * P r x) N]
  split_ifs with h
  · rw [P_eq_primeCounting one_pos, iroot_one]; simp
  · have hx : x < 2 := by simpa [show N = 0 by omega] using hN
    interval_cases x <;> simp

/-! ## The two transforms (M2) for every x -/

lemma modEq_of_eq {n a b : ℤ} (h : a = b) : a ≡ b [ZMOD n] := h ▸ Int.ModEq.refl a

lemma icbrt_zero : icbrt 0 = 0 := Nat.le_zero.1 (icbrt_le 0)

lemma H_zero : H 0 = 0 := by
  have := ternary_M1 0
  simp [D3, icbrt_zero] at this
  omega

lemma Gpp_zero : Gpp 0 = 0 := by simp [Gpp]

/-- **(M2), first transform, for every `x` (including `x = 0`)**:
`G(x) ≡ ∑_{c ≤ x^(1/3)} μ(c) H(⌊x/c^3⌋) (mod 3)`. -/
theorem G_mod_three_all (x : ℕ) :
    Gpp x ≡ ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ) [ZMOD 3] := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [Gpp_zero, icbrt_zero]
  · exact G_mod_three hx

lemma one_le_icbrt {x : ℕ} (hx : 1 ≤ x) : 1 ≤ icbrt x := le_icbrt (by simpa using hx)

/-- **(M2), second transform, for every `x`**: `H(x) ≡ (C_3 G)(x) = ∑_{d ≤ x^(1/3)} G(⌊x/d^3⌋) (mod 3)`. -/
theorem H_mod_three (x : ℕ) :
    (H x : ℤ) ≡ ∑ d ∈ Icc 1 (icbrt x), Gpp (x / d ^ 3) [ZMOD 3] := by
  -- substitute the first transform at every `⌊x/d^3⌋`
  have step : ∑ d ∈ Icc 1 (icbrt x), Gpp (x / d ^ 3)
      ≡ ∑ d ∈ Ioc 0 (icbrt x), ∑ c ∈ Ioc 0 (icbrt x / d), (μ c : ℤ) * (H (x / (d * c) ^ 3) : ℤ)
        [ZMOD 3] := by
    rw [Icc_one_eq_Ioc]
    refine Int.ModEq.sum fun d hd => ?_
    have hd0 : 0 < d := (mem_Ioc.1 hd).1
    have := G_mod_three_all (x / d ^ 3)
    rw [icbrt_div_cube x hd0, Icc_one_eq_Ioc] at this
    refine this.trans (Int.ModEq.refl _ |>.trans ?_)
    refine modEq_of_eq (sum_congr rfl fun c _ => ?_)
    rw [Nat.div_div_eq_div_mul, mul_pow]
  have inv := sum_hyperbola_moebius_inner (fun m => (H (x / m ^ 3) : ℤ)) (icbrt x)
  beta_reduce at inv
  rw [inv] at step
  refine (modEq_of_eq ?_).trans step.symm
  split_ifs with h
  · simp
  · have : x = 0 := by
      by_contra hx; exact h (one_le_icbrt (Nat.one_le_iff_ne_zero.2 hx))
    subst this; simp [H_zero]

/-! ## H mod 3 and D_3 mod 9 determine each other -/

/-- `D_3(x) mod 9` from `H(x) mod 3` and the cube-root term. -/
theorem D3_mod_nine (x : ℕ) : D3 x % 9 = (icbrt x + 3 * (H x % 3)) % 9 := by
  rw [ternary_M1]; omega

/-- `H(x) mod 3` from `D_3(x) mod 9`: subtract the cube-root term modulo 9, take the representative
in `{0, 3, 6}` and divide that integer by 3. -/
theorem H_mod_three_of_D3 (x : ℕ) : H x % 3 = ((D3 x % 9 + 9 - icbrt x % 9) % 9) / 3 := by
  rw [ternary_M1]; omega

/-- The representative of `D_3(x) - ⌊x^(1/3)⌋` modulo 9 lies in `{0, 3, 6}`. -/
theorem D3_sub_mod_nine_mem (x : ℕ) : (D3 x % 9 + 9 - icbrt x % 9) % 9 ∈ ({0, 3, 6} : Finset ℕ) := by
  rw [ternary_M1]
  have : (icbrt x + 3 * H x) % 9 = (icbrt x % 9 + 3 * (H x % 3)) % 9 := by omega
  have h3 : H x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hh : H x % 3 <;> simp <;> omega

/-! ## The reductions as functions -/

/-- `H(y) mod 3` read off a `D_3 mod 9` oracle `o`. -/
def HofD (o : ℕ → ℕ) (y : ℕ) : ZMod 3 := (((o y + 9 - icbrt y % 9) % 9 / 3 : ℕ) : ZMod 3)

/-- First transform of (M2): `G(y) mod 3` from an `H mod 3` oracle `h`. -/
def GofH (h : ℕ → ZMod 3) (y : ℕ) : ZMod 3 :=
  ∑ c ∈ Icc 1 (icbrt y), ((μ c : ℤ) : ZMod 3) * h (y / c ^ 3)

/-- (M4) mod 3: `π(x) mod 3` from a `G mod 3` oracle `g`. -/
def piOfG (g : ℕ → ZMod 3) (x : ℕ) : ZMod 3 :=
  ∑ j ∈ Icc 1 (Nat.log 2 x), ((μ j : ℤ) : ZMod 3) * (j : ZMod 3) * g (iroot j x)

/-- **Forward reduction**: `π(x) mod 3` computed from a `D_3 mod 9` oracle. -/
def piMod3OfD3 (o : ℕ → ℕ) (x : ℕ) : ZMod 3 := piOfG (GofH (HofD o)) x

lemma HofD_correct {o : ℕ → ℕ} {y : ℕ} (ho : o y = D3 y % 9) : HofD o y = (H y : ZMod 3) := by
  rw [HofD, ho, ← H_mod_three_of_D3, ZMod.natCast_mod]

lemma GofH_correct {h : ℕ → ZMod 3} {y : ℕ} (hh : ∀ z ≤ y, h z = (H z : ZMod 3)) :
    GofH h y = ((Gpp y : ℤ) : ZMod 3) := by
  rw [GofH, (ZMod.intCast_eq_intCast_iff _ _ 3).2 (G_mod_three_all y)]
  push_cast
  refine sum_congr rfl fun c _ => ?_
  rw [hh _ (Nat.div_le_self _ _)]

lemma piOfG_correct {g : ℕ → ZMod 3} {x : ℕ} (hg : ∀ y ≤ x, g y = ((Gpp y : ℤ) : ZMod 3)) :
    piOfG g x = (Nat.primeCounting x : ZMod 3) := by
  have h := congrArg (fun z : ℤ => (z : ZMod 3)) (primeCounting_M4 x)
  simp only [Int.cast_natCast] at h
  rw [h, piOfG]
  push_cast
  refine sum_congr rfl fun j hj => ?_
  rw [hg _ (iroot_le (by have := (mem_Icc.1 hj).1; omega) x)]

/-- **Correctness of the forward reduction**: if the oracle returns `D_3(y) mod 9` at every `y ≤ x`,
then `piMod3OfD3 o x = π(x) mod 3`. -/
theorem piMod3OfD3_correct (o : ℕ → ℕ) (x : ℕ) (ho : ∀ y ≤ x, o y = D3 y % 9) :
    piMod3OfD3 o x = (Nat.primeCounting x : ZMod 3) := by
  apply piOfG_correct
  intro y hy
  apply GofH_correct
  intro z hz
  exact HofD_correct (ho z (hz.trans hy))

theorem piMod3OfD3_val (o : ℕ → ℕ) (x : ℕ) (ho : ∀ y ≤ x, o y = D3 y % 9) :
    (piMod3OfD3 o x).val = Nat.primeCounting x % 3 := by
  rw [piMod3OfD3_correct o x ho, ZMod.val_natCast]

/-- `G(y) mod 3` from a `π mod 3` oracle `p`, by (M3)/(M4): `G(y) = ∑_e e π(⌊y^(1/e)⌋)`. -/
def GofPi (p : ℕ → ZMod 3) (y : ℕ) : ZMod 3 :=
  ∑ e ∈ Icc 1 (Nat.log 2 y), (e : ZMod 3) * p (iroot e y)

/-- Second transform of (M2): `H(x) mod 3` from a `G mod 3` oracle `g`. -/
def HofG (g : ℕ → ZMod 3) (x : ℕ) : ZMod 3 := ∑ d ∈ Icc 1 (icbrt x), g (x / d ^ 3)

/-- **Reverse reduction**: `D_3(x) mod 9` computed from a `π mod 3` oracle. -/
def D3mod9OfPi (p : ℕ → ZMod 3) (x : ℕ) : ℕ := (icbrt x + 3 * (HofG (GofPi p) x).val) % 9

lemma GofPi_correct {p : ℕ → ZMod 3} {y : ℕ} (hp : ∀ z ≤ y, p z = (Nat.primeCounting z : ZMod 3)) :
    GofPi p y = ((Gpp y : ℤ) : ZMod 3) := by
  rw [Gpp_eq_sum_primeCounting, GofPi]
  push_cast
  refine sum_congr rfl fun e he => ?_
  rw [hp _ (iroot_le (by have := (mem_Icc.1 he).1; omega) y)]

lemma HofG_correct {g : ℕ → ZMod 3} {x : ℕ} (hg : ∀ y ≤ x, g y = ((Gpp y : ℤ) : ZMod 3)) :
    HofG g x = (H x : ZMod 3) := by
  have h := (ZMod.intCast_eq_intCast_iff _ _ 3).2 (H_mod_three x)
  simp only [Int.cast_natCast] at h
  rw [h, HofG]
  push_cast
  refine sum_congr rfl fun d _ => ?_
  rw [hg _ (Nat.div_le_self _ _)]

/-- **Correctness of the reverse reduction**: if the oracle returns `π(y) mod 3` at every `y ≤ x`,
then `D3mod9OfPi p x = D_3(x) mod 9`. -/
theorem D3mod9OfPi_correct (p : ℕ → ZMod 3) (x : ℕ)
    (hp : ∀ y ≤ x, p y = (Nat.primeCounting y : ZMod 3)) :
    D3mod9OfPi p x = D3 x % 9 := by
  have hH : HofG (GofPi p) x = (H x : ZMod 3) :=
    HofG_correct fun y hy => GofPi_correct fun z hz => hp z (hz.trans hy)
  rw [D3mod9OfPi, hH, ZMod.val_natCast, D3_mod_nine]

/-! ## Director's additions: prime counts at roots, and (I2) at p = 3 -/

/-- The round 3 count `#{q prime : q^k ≤ x}` is `π(⌊x^(1/k)⌋)` for every `k ≥ 1` (in particular `k ≥ 2`). -/
theorem card_primePow_le_eq_primeCounting {k : ℕ} (hk : 0 < k) (x : ℕ) :
    ((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card = Nat.primeCounting (iroot k x) :=
  P_eq_primeCounting hk x

/-- The round 3 statement `primeCounting_mod_three` with prime counts at integer roots: for `x ≥ 1`,
`π(x) + ∑_{2 ≤ e ≤ ⌊log₂ x⌋} e π(⌊x^(1/e)⌋) ≡ ∑_{c ≤ x^(1/3)} μ(c) H(⌊x/c^3⌋) (mod 3)`. -/
theorem primeCounting_mod_three_roots {x : ℕ} (hx : 1 ≤ x) :
    (Nat.primeCounting x : ℤ)
        + ∑ e ∈ Icc 2 (Nat.log 2 x), (e : ℤ) * Nat.primeCounting (iroot e x)
      ≡ ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ) [ZMOD 3] := by
  rw [primeCounting_M3, sub_add_cancel]
  exact G_mod_three hx

lemma zmod3_inv_self : ∀ a : ZMod 3, a⁻¹ = a := by
  intro a
  fin_cases a
  · exact ZMod.inv_zero 3
  · exact inv_eq_of_mul_eq_one_right (by decide)
  · exact inv_eq_of_mul_eq_one_right (by decide)

/-- `G(x) mod 3` in the literal `j⁻¹` weights of (I2) at `p = 3`. -/
theorem Gpp_mod_three_inv (x : ℕ) :
    Gpp x ≡ ∑ j ∈ (Icc 1 (Nat.log 2 x)).filter (fun j => ¬ 3 ∣ j),
        ((((j : ZMod 3)⁻¹).val : ℕ) : ℤ) * Nat.primeCounting (iroot j x) [ZMOD 3] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 3).1
  rw [Gpp_eq_sum_primeCounting, sum_filter]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  by_cases h : 3 ∣ j
  · simp [h, (ZMod.natCast_eq_zero_iff j 3).2 h]
  · simp [h, zmod3_inv_self]

/-- **(I2) at `p = 3` in its literal form**: for `x ≥ 1`,
`S_3(x) ≡ 1 + 3 ∑_{1 ≤ j ≤ ⌊log₂ x⌋, 3 ∤ j} j⁻¹ π(⌊x^(1/j)⌋) (mod 9)`, where `j⁻¹` is the inverse of
`j` modulo 3, represented in `{1, 2}`. -/
theorem S3_I2 {x : ℕ} (hx : 1 ≤ x) :
    S3 x ≡ 1 + 3 * ∑ j ∈ (Icc 1 (Nat.log 2 x)).filter (fun j => ¬ 3 ∣ j),
        ((((j : ZMod 3)⁻¹).val : ℕ) : ℤ) * Nat.primeCounting (iroot j x) [ZMOD 9] := by
  refine (S3_mod_nine hx).trans (Int.ModEq.add_left 1 ?_)
  have := Int.ModEq.mul_left' (c := 3) (Gpp_mod_three_inv x)
  norm_num at this
  exact this

/-- Sanity check on a concrete input: `H(2) = 1` (the three ordered triples with product 2 form one
cyclic orbit), from `D_3(2) = 4` by kernel `decide` and (M1). -/
example : H 2 = 1 := by
  have := ternary_M1 2
  have hc : icbrt 2 = 1 := by
    apply le_antisymm
    · by_contra h; push Not at h; have := (cube_le_iff (x := 2) (k := 2)).2 h; norm_num at this
    · exact le_icbrt (by norm_num)
  have hd : D3 2 = 4 := by decide
  omega

end M2L4
