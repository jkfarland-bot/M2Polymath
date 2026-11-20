/-
  Seat M2L5, item 2: the parity identities (P1) and (P2) of A19 section 9,
  as exact statements for every x.
  (P1): S_2(x) = ∑_{d ≤ U} μ(d) D(⌊x/d²⌋) + ∑_{m ≤ V} τ(m) M(⌊√(x/m)⌋) - M(U) D(V),
        U = ⌊x^(4/11)⌋, V = ⌊x^(3/11)⌋ (and more generally whenever U² V ≤ x < (U+1)² (V+1)).
  (P2): π(x) ≡ (S_2(x) - 1)/2 - ∑_{2 ≤ j ≤ ⌊log₂ x⌋} π(⌊x^(1/j)⌋) (mod 2), x ≥ 1, with the exact
        integer identity S_2(x) = 1 + 2 ∑_{1 ≤ j ≤ ⌊log₂ x⌋} π(⌊x^(1/j)⌋) + 4 K(x) behind it.
-/
import Mathlib
import M2ResultM

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.Moebius
  ArithmeticFunction.omega ArithmeticFunction.Omega

namespace M2L5

open M2L3 M2L4

/-! ## The square dilation `E_2(μ)` and `f_2 = E_2(μ) * τ = 2^ω` -/

/-- `E_2(μ)(n) = μ(c)` if `n = c²`, and `0` if `n` is not a square. -/
def E2mu : ArithmeticFunction ℤ :=
  ⟨fun n => ∑ c ∈ Ioc 0 n, if c ^ 2 = n then μ c else 0, by simp⟩

lemma E2mu_apply (n : ℕ) : E2mu n = ∑ c ∈ Ioc 0 n, if c ^ 2 = n then μ c else 0 := rfl

lemma le_of_sq_le' {c n : ℕ} (h : c ^ 2 ≤ n) : c ≤ n := (Nat.le_self_pow two_ne_zero c).trans h

lemma E2mu_sq {c : ℕ} (hc : 0 < c) : E2mu (c ^ 2) = μ c := by
  rw [E2mu_apply, sum_eq_single_of_mem c ?_ ?_, if_pos rfl]
  · rw [mem_Ioc]; exact ⟨hc, le_of_sq_le' le_rfl⟩
  · intro d _ hdc
    rw [if_neg]
    intro h
    exact hdc (Nat.pow_left_injective (by norm_num) h)

lemma E2mu_nonsq {n : ℕ} (h : ∀ c, c ^ 2 ≠ n) : E2mu n = 0 := by
  rw [E2mu_apply]; exact sum_eq_zero fun c _ => if_neg (h c)

lemma isMultiplicative_E2mu : IsMultiplicative E2mu := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simpa using E2mu_sq (c := 1) one_pos, ?_⟩
  intro m n hm hn hmn
  by_cases hcm : ∃ a, a ^ 2 = m
  · by_cases hcn : ∃ b, b ^ 2 = n
    · obtain ⟨a, rfl⟩ := hcm
      obtain ⟨b, rfl⟩ := hcn
      have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hab : a.Coprime b :=
        (Nat.coprime_pow_right_iff (by norm_num) _ _).1
          ((Nat.coprime_pow_left_iff (by norm_num) _ _).1 hmn)
      rw [← mul_pow, E2mu_sq (Nat.mul_pos ha hb), E2mu_sq ha, E2mu_sq hb,
        isMultiplicative_moebius.map_mul_of_coprime hab]
    · rw [E2mu_nonsq (n := n) (fun b hb => hcn ⟨b, hb⟩), mul_zero]
      apply E2mu_nonsq
      intro c hc
      have hu : IsUnit (gcd n m) := Nat.isUnit_iff.2 (Nat.Coprime.symm hmn)
      obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (by rw [mul_comm]; exact hc.symm)
      exact hcn ⟨d, hd.symm⟩
  · rw [E2mu_nonsq (n := m) (fun a ha => hcm ⟨a, ha⟩), zero_mul]
    apply E2mu_nonsq
    intro c hc
    have hu : IsUnit (gcd m n) := Nat.isUnit_iff.2 hmn
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu hc.symm
    exact hcm ⟨d, hd.symm⟩

/-- At a prime power: `E_2(μ)(q^i) = [i = 0] - [i = 2]`. -/
lemma E2mu_prime_pow {q : ℕ} (hq : q.Prime) (i : ℕ) :
    E2mu (q ^ i) = (if i = 0 then 1 else 0) - (if i = 2 then 1 else 0) := by
  by_cases hsq : ∃ c, c ^ 2 = q ^ i
  · obtain ⟨c, hc⟩ := hsq
    have hcd : c ∣ q ^ i := hc ▸ dvd_pow_self c (by norm_num)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hcd
    rw [← pow_mul] at hc
    have hk : k * 2 = i := Nat.pow_right_injective hq.two_le hc
    rw [← hc, pow_mul, E2mu_sq (pow_pos hq.pos k)]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp at hk; subst hk; simp
      · subst hk; simp [moebius_apply_prime hq]
    · rw [moebius_apply_prime_pow hq (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      simp
  · rw [E2mu_nonsq (fun c hc => hsq ⟨c, hc⟩)]
    have h0 : i ≠ 0 := by rintro rfl; exact hsq ⟨1, by simp⟩
    have h2 : i ≠ 2 := by rintro rfl; exact hsq ⟨q, rfl⟩
    simp [h0, h2]

/-- `f_2 = E_2(μ) * τ`, i.e. `f_2(n) = ∑_{c² ∣ n} μ(c) τ(n / c²)`. -/
def f2 : ArithmeticFunction ℤ := E2mu * ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)

lemma isMultiplicative_f2 : IsMultiplicative f2 :=
  isMultiplicative_E2mu.mul isMultiplicative_sigma.natCast

theorem f2_prime_pow {q : ℕ} (hq : q.Prime) {j : ℕ} (hj : 0 < j) : f2 (q ^ j) = 2 := by
  rw [f2, mul_apply_prime_pow _ _ hq]
  simp only [E2mu_prime_pow hq, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
    sum_ite_eq', mem_range, natCoe_apply, sigma_zero_apply_prime_pow hq]
  rw [if_pos (by omega)]
  simp only [Nat.sub_zero]
  by_cases h2 : 2 < j + 1
  · rw [if_pos h2]; push_cast [show 2 ≤ j by omega]; ring
  · rw [if_neg h2]
    have : j = 1 := by omega
    subst this; norm_num

/-- `f_2(n) = 2^ω(n)` for `n ≥ 1`. -/
theorem f2_eq_two_pow {n : ℕ} (hn0 : n ≠ 0) : f2 n = 2 ^ ω n := by
  rw [isMultiplicative_f2.multiplicative_factorization f2 hn0, Finsupp.prod]
  have : ∀ p ∈ n.factorization.support, f2 (p ^ n.factorization p) = 2 := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact f2_prime_pow hp.1 (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1
      (by rw [Nat.support_factorization, Nat.mem_primeFactors]; exact hp)))
  rw [prod_congr rfl this, prod_const, Nat.support_factorization, card_primeFactors_eq_omega]

/-! ## The summatory functions -/

/-- `S_2(x) = ∑_{n ≤ x} 2^ω(n)`. -/
def S2 (x : ℕ) : ℤ := ∑ n ∈ Ioc 0 x, (2 : ℤ) ^ ω n

/-- `D(y) = D_2(y) = ∑_{n ≤ y} τ(n)`. -/
def D2 (y : ℕ) : ℤ := ∑ n ∈ Ioc 0 y, (σ 0 n : ℤ)

/-- The Mertens function `M(y) = ∑_{d ≤ y} μ(d)`. -/
def Mert (y : ℕ) : ℤ := ∑ d ∈ Ioc 0 y, (μ d : ℤ)

lemma S2_eq_sum_f2 (x : ℕ) : S2 x = ∑ n ∈ Ioc 0 x, f2 n := by
  refine sum_congr rfl fun n hn => ?_
  rw [f2_eq_two_pow (by have := (mem_Ioc.1 hn).1; omega)]

lemma sum_Ioc_le_ite (g : ℕ → ℤ) {A N : ℕ} (h : A ≤ N) :
    ∑ m ∈ Ioc 0 A, g m = ∑ m ∈ Ioc 0 N, if m ≤ A then g m else 0 := by
  rw [← sum_filter]
  congr 1
  ext m; simp only [mem_filter, mem_Ioc]; omega

/-- The square analogue of (F2): `S_2(x) = ∑_{c ≤ x} μ(c) D(⌊x / c²⌋)`. -/
theorem S2_eq_mu_D2 (x : ℕ) : S2 x = ∑ c ∈ Ioc 0 x, μ c * D2 (x / c ^ 2) := by
  rw [S2_eq_sum_f2, f2, sum_Ioc_mul_eq_sum_sum]
  have hD : ∀ d, ∑ m ∈ Ioc 0 (x / d), ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) m
      = D2 (x / d) := by intro d; simp [D2, natCoe_apply]
  simp only [hD, E2mu_apply, sum_mul]
  have ext : ∀ d ∈ Ioc 0 x, ∑ c ∈ Ioc 0 d, (if c ^ 2 = d then (μ c : ℤ) else 0) * D2 (x / d)
      = ∑ c ∈ Ioc 0 x, (if c ^ 2 = d then (μ c : ℤ) else 0) * D2 (x / d) := by
    intro d hd
    apply sum_subset (Ioc_subset_Ioc_right (mem_Ioc.1 hd).2)
    intro c hc hcd
    rw [mem_Ioc] at hc hcd
    have : c ^ 2 ≠ d := by
      intro h; apply hcd ⟨hc.1, ?_⟩; rw [← h]; exact le_of_sq_le' le_rfl
    simp [this]
  rw [sum_congr rfl ext, sum_comm]
  refine sum_congr rfl fun c hc => ?_
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq]
  have hc0 : 0 < c := (mem_Ioc.1 hc).1
  by_cases hm : c ^ 2 ≤ x
  · rw [if_pos (mem_Ioc.2 ⟨pow_pos hc0 2, hm⟩)]
  · rw [if_neg (fun h => hm (mem_Ioc.1 h).2), Nat.div_eq_of_lt (by omega)]
    simp [D2]

/-- `D(⌊x / c²⌋)` as a sum over the box `m ≤ x` with the indicator `[c² m ≤ x]`. -/
lemma D2_box (x c : ℕ) (hc : 0 < c) :
    D2 (x / c ^ 2) = ∑ m ∈ Ioc 0 x, if c ^ 2 * m ≤ x then (σ 0 m : ℤ) else 0 := by
  rw [D2, sum_Ioc_le_ite _ (Nat.div_le_self x (c ^ 2))]
  refine sum_congr rfl fun m _ => ?_
  exact if_congr (by rw [Nat.le_div_iff_mul_le (pow_pos hc 2), mul_comm]) rfl rfl

/-- `M(⌊√(x/m)⌋)` as a sum over the box `c ≤ x` with the indicator `[c² m ≤ x]`. -/
lemma Mert_box (x m : ℕ) (hm : 0 < m) :
    Mert (Nat.sqrt (x / m)) = ∑ c ∈ Ioc 0 x, if c ^ 2 * m ≤ x then (μ c : ℤ) else 0 := by
  rw [Mert, sum_Ioc_le_ite _ ((Nat.sqrt_le_self _).trans (Nat.div_le_self x m))]
  refine sum_congr rfl fun c _ => ?_
  exact if_congr (by rw [Nat.le_sqrt, Nat.le_div_iff_mul_le hm, sq]) rfl rfl

/-- **(P1), general form.** For `U, V ≥ 1` with `U² V ≤ x < (U+1)² (V+1)`:
`S_2(x) = ∑_{d ≤ U} μ(d) D(⌊x/d²⌋) + ∑_{m ≤ V} τ(m) M(⌊√(x/m)⌋) - M(U) D(V)`. -/
theorem P1_general {x U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hlo : U ^ 2 * V ≤ x)
    (hhi : x < (U + 1) ^ 2 * (V + 1)) :
    S2 x = ∑ d ∈ Icc 1 U, μ d * D2 (x / d ^ 2)
      + ∑ m ∈ Icc 1 V, (σ 0 m : ℤ) * Mert (Nat.sqrt (x / m)) - Mert U * D2 V := by
  have hUx : U ≤ x := by nlinarith
  have hVx : V ≤ x := by have : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ hU; nlinarith
  rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc]
  -- everything as box sums
  set B : ℕ → ℕ → ℤ := fun c m => if c ^ 2 * m ≤ x then (μ c : ℤ) * (σ 0 m : ℤ) else 0
  have hS : S2 x = ∑ c ∈ Ioc 0 x, ∑ m ∈ Ioc 0 x, B c m := by
    rw [S2_eq_mu_D2]
    refine sum_congr rfl fun c hc => ?_
    rw [D2_box x c (mem_Ioc.1 hc).1, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    simp only [B]; split_ifs <;> simp
  have hT1 : ∑ d ∈ Ioc 0 U, μ d * D2 (x / d ^ 2)
      = ∑ c ∈ Ioc 0 x, ∑ m ∈ Ioc 0 x, if c ≤ U then B c m else 0 := by
    rw [sum_Ioc_le_ite _ hUx]
    refine sum_congr rfl fun c hc => ?_
    by_cases h : c ≤ U
    · simp only [if_pos h]
      rw [D2_box x c (mem_Ioc.1 hc).1, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      simp only [B]; split_ifs <;> simp
    · simp [h]
  have hT2 : ∑ m ∈ Ioc 0 V, (σ 0 m : ℤ) * Mert (Nat.sqrt (x / m))
      = ∑ c ∈ Ioc 0 x, ∑ m ∈ Ioc 0 x, if m ≤ V then B c m else 0 := by
    rw [sum_comm, sum_Ioc_le_ite _ hVx]
    refine sum_congr rfl fun m hm => ?_
    by_cases h : m ≤ V
    · simp only [if_pos h]
      rw [Mert_box x m (mem_Ioc.1 hm).1, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      simp only [B]; split_ifs <;> ring
    · simp [h]
  have hT3 : Mert U * D2 V
      = ∑ c ∈ Ioc 0 x, ∑ m ∈ Ioc 0 x, if c ≤ U ∧ m ≤ V then (μ c : ℤ) * (σ 0 m : ℤ) else 0 := by
    rw [Mert, D2, sum_Ioc_le_ite _ hUx, sum_Ioc_le_ite _ hVx, sum_mul_sum]
    refine sum_congr rfl fun c _ => sum_congr rfl fun m _ => ?_
    by_cases h1 : c ≤ U <;> by_cases h2 : m ≤ V <;> simp [h1, h2]
  rw [hS, hT1, hT2, hT3, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun c hc => ?_
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun m hm => ?_
  have hc0 := (mem_Ioc.1 hc).1
  have hm0 := (mem_Ioc.1 hm).1
  simp only [B]
  by_cases h1 : c ≤ U <;> by_cases h2 : m ≤ V
  · have : c ^ 2 * m ≤ x := le_trans (Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) h2) hlo
    simp [h1, h2, this]
  · simp [h1, h2]
  · simp [h1, h2]
  · have : ¬ c ^ 2 * m ≤ x := by
      intro h
      have := Nat.mul_le_mul (Nat.pow_le_pow_left (show U + 1 ≤ c by omega) 2) (show V + 1 ≤ m by omega)
      omega
    simp [h1, h2, this]

/-- `⌊x^(a/k)⌋` as the integer root `iroot k (x^a)`. -/
theorem iroot_pow_eq_floor {k : ℕ} (hk : 0 < k) (a x : ℕ) :
    iroot k (x ^ a) = ⌊(x : ℝ) ^ ((a : ℝ) / k)⌋₊ := by
  rw [iroot_eq_floor hk, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  field_simp

/-- **(P1)** for every natural `x`, with `U = ⌊x^(4/11)⌋` and `V = ⌊x^(3/11)⌋` (integer roots):
`S_2(x) = ∑_{d ≤ U} μ(d) D(⌊x/d²⌋) + ∑_{m ≤ V} τ(m) M(⌊√(x/m)⌋) - M(U) D(V)`. -/
theorem P1 (x : ℕ) :
    S2 x = ∑ d ∈ Icc 1 (iroot 11 (x ^ 4)), μ d * D2 (x / d ^ 2)
      + ∑ m ∈ Icc 1 (iroot 11 (x ^ 3)), (σ 0 m : ℤ) * Mert (Nat.sqrt (x / m))
      - Mert (iroot 11 (x ^ 4)) * D2 (iroot 11 (x ^ 3)) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have h0 : iroot 11 (0 ^ 4) = 0 := by
      have := iroot_le (k := 11) (by norm_num) (0 ^ 4); simp at this ⊢; omega
    have h0' : iroot 11 (0 ^ 3) = 0 := by
      have := iroot_le (k := 11) (by norm_num) (0 ^ 3); simp at this ⊢; omega
    rw [h0, h0']; simp [S2, Mert, D2]
  set U := iroot 11 (x ^ 4)
  set V := iroot 11 (x ^ 3)
  have hk : (0 : ℕ) < 11 := by norm_num
  have hU1 : 1 ≤ U := (pow_le_iff_le_iroot hk).1 (by simp; exact Nat.one_le_pow _ _ hx)
  have hV1 : 1 ≤ V := (pow_le_iff_le_iroot hk).1 (by simp; exact Nat.one_le_pow _ _ hx)
  have hUp : U ^ 11 ≤ x ^ 4 := iroot_pow_le hk _
  have hVp : V ^ 11 ≤ x ^ 3 := iroot_pow_le hk _
  have hUq : x ^ 4 < (U + 1) ^ 11 := by
    by_contra h; push Not at h; have := (pow_le_iff_le_iroot hk).1 h; omega
  have hVq : x ^ 3 < (V + 1) ^ 11 := by
    by_contra h; push Not at h; have := (pow_le_iff_le_iroot hk).1 h; omega
  apply P1_general hU1 hV1
  · have : (U ^ 2 * V) ^ 11 ≤ x ^ 11 := by
      calc (U ^ 2 * V) ^ 11 = (U ^ 11) ^ 2 * V ^ 11 := by ring
        _ ≤ (x ^ 4) ^ 2 * x ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hUp 2) hVp
        _ = x ^ 11 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  · have : x ^ 11 < ((U + 1) ^ 2 * (V + 1)) ^ 11 := by
      calc x ^ 11 = (x ^ 4) ^ 2 * x ^ 3 := by ring
        _ < ((U + 1) ^ 11) ^ 2 * (V + 1) ^ 11 :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_left hUq (by norm_num)) hVq.le (by positivity)
        _ = ((U + 1) ^ 2 * (V + 1)) ^ 11 := by ring
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 this

/-- **(P1)** with `U` and `V` written as real floors `⌊x^(4/11)⌋`, `⌊x^(3/11)⌋`. -/
theorem P1_real (x : ℕ) :
    S2 x = ∑ d ∈ Icc 1 ⌊(x : ℝ) ^ ((4 : ℝ) / 11)⌋₊, μ d * D2 (x / d ^ 2)
      + ∑ m ∈ Icc 1 ⌊(x : ℝ) ^ ((3 : ℝ) / 11)⌋₊, (σ 0 m : ℤ) * Mert (Nat.sqrt (x / m))
      - Mert ⌊(x : ℝ) ^ ((4 : ℝ) / 11)⌋₊ * D2 ⌊(x : ℝ) ^ ((3 : ℝ) / 11)⌋₊ := by
  have h4 := iroot_pow_eq_floor (k := 11) (by norm_num) 4 x
  have h3 := iroot_pow_eq_floor (k := 11) (by norm_num) 3 x
  push_cast at h4 h3
  rw [← h4, ← h3]; exact P1 x

/-! ## (P2) -/

/-- Pointwise: `2^ω(n) = [n = 1] + 2 [n prime power] + 4 [ω(n) ≥ 2] 2^(ω(n) - 2)` for `n ≥ 1`. -/
lemma two_pow_omega_split {n : ℕ} (hn : 0 < n) :
    (2 : ℤ) ^ ω n = (if n = 1 then 1 else 0) + 2 * (if IsPrimePow n then 1 else 0)
      + 4 * (if 2 ≤ ω n then 2 ^ (ω n - 2) else 0) := by
  by_cases h1 : n = 1
  · subst h1; simp [not_isPrimePow_one]
  have h0 : ω n ≠ 0 := by rw [Ne, cardDistinctFactors_eq_zero]; omega
  by_cases hpp : IsPrimePow n
  · have : ω n = 1 := cardDistinctFactors_eq_one_iff.2 hpp
    simp [h1, hpp, this]
  · have h1' : ω n ≠ 1 := fun h => hpp (cardDistinctFactors_eq_one_iff.1 h)
    have h2 : 2 ≤ ω n := by omega
    simp only [h1, hpp, if_false, if_pos h2]
    rw [show ω n = (ω n - 2) + 2 by omega, pow_add]
    simp; ring

/-- The number of prime powers `q^e ≤ x` (`e ≥ 1`) is `∑_{1 ≤ e ≤ ⌊log₂ x⌋} π(⌊x^(1/e)⌋)`. -/
theorem card_primePow_eq_sum (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if IsPrimePow n then (1 : ℤ) else 0)
      = ∑ e ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (iroot e x) : ℤ) := by
  have h := sum_primePow_weight (fun _ => (1 : ℤ)) x
  simp only [one_mul] at h
  rw [h]
  have hz : ∀ k, min x (Nat.log 2 x) < k → ((P k x : ℕ) : ℤ) = 0 := by
    intro k hk
    rw [P_eq_zero, Nat.cast_zero]
    rcases min_lt_iff.1 hk with h | h
    · exact lt_of_le_of_lt (Nat.lt_two_pow_self).le (Nat.pow_lt_pow_right (by norm_num) h)
    · exact lt_of_lt_of_le (lt_two_pow_log x) (Nat.pow_le_pow_right (by norm_num) h)
  change ∑ k ∈ Ioc 0 x, ((P k x : ℕ) : ℤ) = _
  rw [sum_Ioc_trim _ (min_le_left x _) hz, ← sum_Ioc_trim _ (min_le_right x _) hz,
    Icc_one_eq_Ioc]
  refine sum_congr rfl fun e he => ?_
  rw [P_eq_primeCounting (mem_Ioc.1 he).1]

/-- **The exact identity behind (P2)**, for `x ≥ 1`:
`S_2(x) = 1 + 2 ∑_{1 ≤ j ≤ ⌊log₂ x⌋} π(⌊x^(1/j)⌋) + 4 K(x)`, `K(x) = ∑_{n ≤ x, ω(n) ≥ 2} 2^(ω(n) - 2)`. -/
theorem S2_exact {x : ℕ} (hx : 1 ≤ x) :
    S2 x = 1 + 2 * ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (iroot j x) : ℤ)
      + 4 * ∑ n ∈ Ioc 0 x, (if 2 ≤ ω n then (2 : ℤ) ^ (ω n - 2) else 0) := by
  rw [S2, sum_congr rfl fun n hn => two_pow_omega_split (mem_Ioc.1 hn).1, sum_add_distrib,
    sum_add_distrib, ← mul_sum, ← mul_sum, card_primePow_eq_sum, sum_ite_eq']
  simp [hx]

/-- **(P2)** for every `x ≥ 1`: `π(x) ≡ (S_2(x) - 1)/2 - ∑_{2 ≤ j ≤ ⌊log₂ x⌋} π(⌊x^(1/j)⌋) (mod 2)`.
(At `x = 0` the quotient `(S_2(0) - 1)/2 = -1/2` is not an integer, so `x ≥ 1` is needed.) -/
theorem P2 {x : ℕ} (hx : 1 ≤ x) :
    (Nat.primeCounting x : ℤ)
      ≡ (S2 x - 1) / 2 - ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting (iroot j x) : ℤ) [ZMOD 2] := by
  set K := ∑ n ∈ Ioc 0 x, (if 2 ≤ ω n then (2 : ℤ) ^ (ω n - 2) else 0)
  set A := ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (iroot j x) : ℤ)
  have hS : (S2 x - 1) / 2 = A + 2 * K := by
    rw [S2_exact hx, show 1 + 2 * A + 4 * K - 1 = 2 * (A + 2 * K) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  have hA : A = Nat.primeCounting x + ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting (iroot j x) : ℤ) := by
    by_cases hx1 : x = 1
    · subst hx1; simp [A]
    · have hl : 1 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have : Icc 1 (Nat.log 2 x) = insert 1 (Icc 2 (Nat.log 2 x)) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [show A = ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (iroot j x) : ℤ) from rfl, this,
        sum_insert (by simp), iroot_one]
  rw [hS, hA, Int.modEq_iff_dvd]
  exact ⟨K, by ring⟩

end M2L5
