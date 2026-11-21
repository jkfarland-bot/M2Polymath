module

public import Mathlib
public import M2Ternary

/-!
  Seat M2L3, item 2: the Polymath-type mod 3 identity (A19 (I1) at p = 3, (F2), (M2)).
  f_3 = E_3(μ) * d_3 has f_3(1) = 1, f_3(q^j) = 3 j exactly, and f_3(n) ≡ 0 (mod 9) when
  ω(n) ≥ 2.  Summed: S_3(x) = ∑_{c ≤ x^(1/3)} μ(c) D_3(⌊x/c^3⌋) ≡ 1 + 3 G(x) (mod 9),
  G(x) = ∑_{q^e ≤ x} e, and G(x) ≡ ∑_{c ≤ x^(1/3)} μ(c) H(⌊x/c^3⌋) (mod 3).
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.Moebius
  ArithmeticFunction.omega ArithmeticFunction.Omega

namespace M2L3

/-! ## The cube dilation `E_3(μ)` -/

/-- `E_3(μ)(n) = μ(c)` if `n = c^3`, and `0` if `n` is not a cube. -/
def E3mu : ArithmeticFunction ℤ :=
  ⟨fun n => ∑ c ∈ Ioc 0 n, if c ^ 3 = n then μ c else 0, by simp⟩

lemma E3mu_apply (n : ℕ) : E3mu n = ∑ c ∈ Ioc 0 n, if c ^ 3 = n then μ c else 0 := rfl

lemma E3mu_cube {c : ℕ} (hc : 0 < c) : E3mu (c ^ 3) = μ c := by
  rw [E3mu_apply, sum_eq_single_of_mem c ?_ ?_, ite_eq_left rfl]
  · rw [mem_Ioc]; exact ⟨hc, le_of_cube_le le_rfl⟩
  · intro d _ hdc
    rw [ite_eq_right]
    intro h
    exact hdc (Nat.pow_left_injective (by norm_num) h)

lemma E3mu_noncube {n : ℕ} (h : ∀ c, c ^ 3 ≠ n) : E3mu n = 0 := by
  rw [E3mu_apply]; exact sum_eq_zero fun c _ => ite_eq_right (h c)

lemma isMultiplicative_E3mu : IsMultiplicative E3mu := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simpa using E3mu_cube (c := 1) one_pos, ?_⟩
  intro m n hm hn hmn
  by_cases hcm : ∃ a, a ^ 3 = m
  · by_cases hcn : ∃ b, b ^ 3 = n
    · obtain ⟨a, rfl⟩ := hcm
      obtain ⟨b, rfl⟩ := hcn
      have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hab : a.Coprime b :=
        (Nat.coprime_pow_right_iff (by norm_num) _ _).1
          ((Nat.coprime_pow_left_iff (by norm_num) _ _).1 hmn)
      rw [← mul_pow, E3mu_cube (Nat.mul_pos ha hb), E3mu_cube ha, E3mu_cube hb,
        isMultiplicative_moebius.map_mul_of_coprime hab]
    · rw [E3mu_noncube (n := n) (fun b hb => hcn ⟨b, hb⟩), mul_zero]
      apply E3mu_noncube
      intro c hc
      have hu : IsUnit (gcd n m) := Nat.isUnit_iff.2 (Nat.Coprime.symm hmn)
      obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (by rw [mul_comm]; exact hc.symm)
      exact hcn ⟨d, hd.symm⟩
  · rw [E3mu_noncube (n := m) (fun a ha => hcm ⟨a, ha⟩), zero_mul]
    apply E3mu_noncube
    intro c hc
    have hu : IsUnit (gcd m n) := Nat.isUnit_iff.2 hmn
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu hc.symm
    exact hcm ⟨d, hd.symm⟩

/-- At a prime power: `E_3(μ)(q^i) = [i = 0] - [i = 3]`. -/
lemma E3mu_prime_pow {q : ℕ} (hq : q.Prime) (i : ℕ) :
    E3mu (q ^ i) = (if i = 0 then 1 else 0) - (if i = 3 then 1 else 0) := by
  by_cases hcube : ∃ c, c ^ 3 = q ^ i
  · obtain ⟨c, hc⟩ := hcube
    have hcd : c ∣ q ^ i := hc ▸ dvd_pow_self c (by norm_num)
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hcd
    rw [← pow_mul] at hc
    have hk : k * 3 = i := Nat.pow_right_injective hq.two_le hc
    rw [← hc, pow_mul, E3mu_cube (pow_pos hq.pos k)]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp at hk; subst hk; simp
      · subst hk; simp [moebius_apply_prime hq]
    · rw [moebius_apply_prime_pow hq (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp
  · rw [E3mu_noncube (fun c hc => hcube ⟨c, hc⟩)]
    have h0 : i ≠ 0 := by rintro rfl; exact hcube ⟨1, by simp⟩
    have h3 : i ≠ 3 := by rintro rfl; exact hcube ⟨q, rfl⟩
    simp [h0, h3]

/-! ## `d_3` at prime powers -/

/-- Dirichlet convolution at a prime power. -/
lemma mul_apply_prime_pow {R : Type*} [CommSemiring R] (f g : ArithmeticFunction R) {q : ℕ}
    (hq : q.Prime) (j : ℕ) :
    (f * g) (q ^ j) = ∑ i ∈ range (j + 1), f (q ^ i) * g (q ^ (j - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hq]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hq.pos]

lemma two_mul_sum_succ (j : ℕ) : 2 * ∑ i ∈ range (j + 1), (i + 1) = (j + 1) * (j + 2) := by
  induction j with
  | zero => simp
  | succ k ih => rw [sum_range_succ, mul_add, ih]; ring

lemma d3_prime_pow_two_mul {q : ℕ} (hq : q.Prime) (j : ℕ) :
    2 * d3 (q ^ j) = (j + 1) * (j + 2) := by
  rw [d3_eq_sigma0_mul_zeta, mul_apply_prime_pow _ _ hq]
  have : ∀ i ∈ range (j + 1), σ 0 (q ^ i) * ζ (q ^ (j - i)) = i + 1 := by
    intro i _
    rw [sigma_zero_apply_prime_pow hq, zeta_apply, ite_eq_right (pow_ne_zero _ hq.ne_zero), mul_one]
  rw [sum_congr rfl this, two_mul_sum_succ]

/-! ## `f_3 = E_3(μ) * d_3` -/

/-- The A19 function `f_3 = E_3(μ) * d_3` (equation (I1) at `p = 3`). -/
def f3 : ArithmeticFunction ℤ := E3mu * (d3 : ArithmeticFunction ℤ)

/-- The literal form: `f_3(n) = ∑_{c^3 ∣ n} μ(c) d_3(n / c^3)`. -/
theorem f3_apply (n : ℕ) :
    f3 n = ∑ c ∈ n.divisors.filter (fun c => c ^ 3 ∣ n), μ c * (d3 (n / c ^ 3) : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [f3, mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => E3mu a * (d3 : ArithmeticFunction ℤ) b)]
  simp only [E3mu_apply, sum_mul, natCoe_apply]
  have step : ∀ u ∈ n.divisors, ∑ c ∈ Ioc 0 u, (if c ^ 3 = u then (μ c : ℤ) else 0) * (d3 (n / u) : ℤ)
      = ∑ c ∈ n.divisors, (if c ^ 3 = u then (μ c : ℤ) else 0) * (d3 (n / u) : ℤ) := by
    intro u hu
    have hun : u ∣ n := Nat.dvd_of_mem_divisors hu
    have hul : u ≤ n := Nat.le_of_dvd hn hun
    have hz : ∀ c, c ^ 3 ≠ u → (if c ^ 3 = u then (μ c : ℤ) else 0) * (d3 (n / u) : ℤ) = 0 :=
      fun c hc => by rw [ite_eq_right hc, zero_mul]
    rw [sum_subset (Ioc_subset_Ioc_right hul) (fun c _ hc => hz c (by
      intro h; apply hc; rw [mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h; subst h; simp at hu),
        h ▸ le_of_cube_le le_rfl⟩))]
    symm
    apply sum_subset
    · intro c hc; rw [mem_Ioc]; exact ⟨Nat.pos_of_mem_divisors hc, Nat.divisor_le hc⟩
    · intro c _ hc
      apply hz
      intro h; apply hc
      rw [Nat.mem_divisors]
      exact ⟨(Dvd.intro (c ^ 2) (by rw [← h]; ring)).trans hun, hn.ne'⟩
  rw [sum_congr rfl step, sum_comm, sum_filter]
  refine sum_congr rfl fun c _ => ?_
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq]
  simp only [Nat.mem_divisors, ne_eq, hn.ne', not_false_eq_true, and_true]

lemma isMultiplicative_d3 : IsMultiplicative d3 :=
  (isMultiplicative_zeta.mul isMultiplicative_zeta).mul isMultiplicative_zeta

lemma isMultiplicative_f3 : IsMultiplicative f3 :=
  isMultiplicative_E3mu.mul isMultiplicative_d3.natCast

theorem f3_one : f3 1 = 1 := isMultiplicative_f3.map_one

/-- **(I1) at p = 3**: `f_3(q^j) = 3 j` exactly, for every prime `q` and `j ≥ 1`
(the local coefficient `binom(j+2,2) - binom(j-1,2)`). -/
theorem f3_prime_pow {q : ℕ} (hq : q.Prime) {j : ℕ} (hj : 0 < j) : f3 (q ^ j) = 3 * j := by
  rw [f3, mul_apply_prime_pow _ _ hq]
  simp only [E3mu_prime_pow hq, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
    sum_ite_eq', mem_range, natCoe_apply]
  have hd : ∀ k : ℕ, (2 : ℤ) * (d3 (q ^ k) : ℤ) = ((k : ℤ) + 1) * ((k : ℤ) + 2) := by
    intro k; exact_mod_cast d3_prime_pow_two_mul hq k
  rw [ite_eq_left (by omega)]
  simp only [Nat.sub_zero]
  by_cases h3 : 3 < j + 1
  · rw [ite_eq_left h3]
    have e := hd j
    have e3 := hd (j - 3)
    push_cast [show 3 ≤ j by omega] at e3
    linarith
  · rw [ite_eq_right h3]
    have e := hd j
    have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl <;> push_cast at e ⊢ <;> linarith

lemma card_primeFactors_eq_omega (n : ℕ) : n.primeFactors.card = ω n := by
  rw [cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- **Pointwise mod 9**: `f_3(n) ≡ 0 (mod 9)` whenever `n` has at least two distinct prime
factors. -/
theorem f3_dvd_nine {n : ℕ} (hn : 2 ≤ ω n) : (9 : ℤ) ∣ f3 n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [isMultiplicative_f3.multiplicative_factorization f3 hn0, Finsupp.prod]
  have : ∀ p ∈ n.factorization.support, f3 (p ^ n.factorization p) = 3 * n.factorization p := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact f3_prime_pow hp.1 (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1
      (by rw [Nat.support_factorization, Nat.mem_primeFactors]; exact hp)))
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, Nat.support_factorization,
    card_primeFactors_eq_omega]
  exact Dvd.dvd.mul_right (by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ∣ 3 ^ ω n := pow_dvd_pow 3 hn) _

/-- **Pointwise form of (I1) mod 9**, for every `n ≥ 1`:
`f_3(n) ≡ [n = 1] + 3 [n is a prime power] Ω(n) (mod 9)`. -/
theorem f3_mod_nine {n : ℕ} (hn : 0 < n) :
    f3 n ≡ (if n = 1 then 1 else 0) + 3 * (if IsPrimePow n then (Ω n : ℤ) else 0) [ZMOD 9] := by
  by_cases h1 : n = 1
  · subst h1; simp [f3_one, not_isPrimePow_one]
  rw [ite_eq_right h1]
  by_cases hpp : IsPrimePow n
  · rw [ite_eq_left hpp]
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    rw [← Nat.prime_iff] at hp
    rw [f3_prime_pow hp hk, cardFactors_apply_prime_pow hp]
    simp
  · rw [ite_eq_right hpp, Int.modEq_iff_dvd]
    have h2 : 2 ≤ ω n := by
      have h0 : ω n ≠ 0 := by rw [Ne, cardDistinctFactors_eq_zero]; omega
      have h1' : ω n ≠ 1 := fun h => hpp (cardDistinctFactors_eq_one_iff.1 h)
      omega
    simpa using f3_dvd_nine h2

/-! ## Summed forms -/

/-- `S_3(x) = ∑_{n ≤ x} f_3(n)`. -/
def S3 (x : ℕ) : ℤ := ∑ n ∈ Ioc 0 x, f3 n

/-- `G(x) = ∑_{q prime, e ≥ 1, q^e ≤ x} e`, written as `∑_{n ≤ x, n prime power} Ω(n)`. -/
def Gpp (x : ℕ) : ℤ := ∑ n ∈ Ioc 0 x, if IsPrimePow n then (Ω n : ℤ) else 0

/-- **Summed (I1) at p = 3**: `S_3(x) ≡ 1 + 3 G(x) (mod 9)` for `x ≥ 1`. -/
theorem S3_mod_nine {x : ℕ} (hx : 1 ≤ x) : S3 x ≡ 1 + 3 * Gpp x [ZMOD 9] := by
  have h1 : (1 : ℤ) = ∑ n ∈ Ioc 0 x, (if n = 1 then 1 else 0) := by
    rw [sum_ite_eq']; simp [hx]
  rw [S3, Gpp, h1, mul_sum, ← sum_add_distrib]
  rw [Int.modEq_iff_dvd, ← sum_sub_distrib]
  apply dvd_sum
  intro n hn
  have := f3_mod_nine (mem_Ioc.1 hn).1
  rw [Int.modEq_iff_dvd] at this
  exact this

lemma sum_cast_d3 (y : ℕ) : ∑ m ∈ Ioc 0 y, (d3 : ArithmeticFunction ℤ) m = (D3 y : ℤ) := by
  simp [D3, natCoe_apply]

/-- **(F2)**: `S_3(x) = ∑_{c ≤ x^(1/3)} μ(c) D_3(⌊x / c^3⌋)`, an exact identity. -/
theorem S3_eq (x : ℕ) :
    S3 x = ∑ c ∈ Icc 1 (icbrt x), μ c * (D3 (x / c ^ 3) : ℤ) := by
  rw [S3, f3, sum_Ioc_mul_eq_sum_sum]
  simp only [sum_cast_d3, E3mu_apply, sum_mul]
  -- extend the inner range from `(0, d]` to `(0, x]`
  have ext : ∀ d ∈ Ioc 0 x, ∑ c ∈ Ioc 0 d, (if c ^ 3 = d then (μ c : ℤ) else 0) * (D3 (x / d) : ℤ)
      = ∑ c ∈ Ioc 0 x, (if c ^ 3 = d then (μ c : ℤ) else 0) * (D3 (x / d) : ℤ) := by
    intro d hd
    apply sum_subset (Ioc_subset_Ioc_right (mem_Ioc.1 hd).2)
    intro c hc hcd
    rw [mem_Ioc] at hc hcd
    have : c ^ 3 ≠ d := by
      intro h; apply hcd ⟨hc.1, ?_⟩; rw [← h]; exact le_of_cube_le le_rfl
    simp [this]
  rw [sum_congr rfl ext, sum_comm]
  simp only [ite_mul, zero_mul]
  rw [← restrict_icbrt_ite]
  refine sum_congr rfl fun c hc => ?_
  rw [sum_ite_eq]
  have hc0 : 0 < c := (mem_Ioc.1 hc).1
  by_cases hm : c ≤ icbrt x
  · rw [ite_eq_left hm, ite_eq_left]
    rw [mem_Ioc]
    exact ⟨pow_pos hc0 3, cube_le_iff.2 hm⟩
  · rw [ite_eq_right hm, ite_eq_right]
    rw [mem_Ioc]
    exact fun h => hm (cube_le_iff.1 h.2)

/-- Nested floors of cube roots: `icbrt (⌊x / c^3⌋) = ⌊icbrt x / c⌋`. -/
lemma icbrt_div_cube (x : ℕ) {c : ℕ} (hc : 0 < c) : icbrt (x / c ^ 3) = icbrt x / c := by
  apply eq_of_forall_le_iff
  intro k
  rw [← cube_le_iff, Nat.le_div_iff_mul_le (pow_pos hc 3), Nat.le_div_iff_mul_le hc,
    ← cube_le_iff, mul_pow]

/-- `∑_{c ≤ m} μ(c) ⌊m / c⌋ = 1` for `m ≥ 1`. -/
lemma sum_moebius_floor {m : ℕ} (hm : 1 ≤ m) :
    ∑ c ∈ Icc 1 m, (μ c : ℤ) * ((m / c : ℕ) : ℤ) = 1 := by
  have h := sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℤ) m
  rw [moebius_mul_coe_zeta] at h
  have hI : Icc 1 m = Ioc 0 m := by ext c; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI, ← h, sum_eq_single_of_mem 1 (by simp; omega)]
  · simp
  · intro b _ hb; simp [hb]

/-- **(M2), first transform**: for `x ≥ 1`,
`G(x) ≡ ∑_{c ≤ x^(1/3)} μ(c) H(⌊x / c^3⌋) (mod 3)`. -/
theorem G_mod_three {x : ℕ} (hx : 1 ≤ x) :
    Gpp x ≡ ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ) [ZMOD 3] := by
  have hm : 1 ≤ icbrt x := le_icbrt (by simpa using hx)
  have hS : S3 x = 1 + 3 * ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ) := by
    rw [S3_eq]
    have : ∀ c ∈ Icc 1 (icbrt x), (μ c : ℤ) * (D3 (x / c ^ 3) : ℤ)
        = μ c * ((icbrt x / c : ℕ) : ℤ) + 3 * (μ c * (H (x / c ^ 3) : ℤ)) := by
      intro c hc
      rw [ternary_M1, icbrt_div_cube x (by have := (mem_Icc.1 hc).1; omega)]
      push_cast; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_moebius_floor hm, ← mul_sum]
  have h9 := S3_mod_nine hx
  rw [hS] at h9
  have : (3 : ℤ) * 3 ∣ 3 * (Gpp x - ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ)) := by
    have := (Int.modEq_iff_dvd.1 h9)
    rw [show (9 : ℤ) = 3 * 3 by norm_num] at this
    rw [show (3 : ℤ) * (Gpp x - ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ))
      = 1 + 3 * Gpp x - (1 + 3 * ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ)) by ring]
    exact this
  exact (Int.modEq_iff_dvd.2 (Int.dvd_of_mul_dvd_mul_left (by norm_num) this)).symm

/-! ## `G(x)` through prime counts -/

/-- Pointwise decomposition of a prime-power weight `w(Ω n)` over pairs `(k, p)` with `p^k = n`. -/
lemma ppow_pointwise_w (w : ℕ → ℤ) {x n : ℕ} (hn : n ∈ Ioc 0 x) :
    (if IsPrimePow n then w (Ω n) else 0)
      = ∑ k ∈ Ioc 0 x, ∑ p ∈ Ioc 0 x, (if p ^ k = n ∧ p.Prime then w k else 0) := by
  rw [mem_Ioc] at hn
  by_cases hpp : IsPrimePow n
  · rw [ite_eq_left hpp]
    obtain ⟨p0, k0, hp0, hk0, rfl⟩ := hpp
    rw [← Nat.prime_iff] at hp0
    rw [cardFactors_apply_prime_pow hp0]
    have hk0x : k0 ∈ Ioc 0 x := mem_Ioc.2 ⟨hk0, (Nat.lt_pow_self hp0.one_lt).le.trans hn.2⟩
    have hp0x : p0 ∈ Ioc 0 x :=
      mem_Ioc.2 ⟨hp0.pos, (Nat.le_self_pow hk0.ne' p0).trans hn.2⟩
    rw [sum_eq_single_of_mem k0 hk0x, sum_eq_single_of_mem p0 hp0x, ite_eq_left ⟨rfl, hp0⟩]
    · intro p _ hp
      rw [ite_eq_right]
      rintro ⟨h, hpr⟩
      exact hp (hpr.pow_inj' hp0 hk0.ne' hk0.ne' h).1
    · intro k hk hkk
      apply sum_eq_zero
      intro p _
      rw [ite_eq_right]
      rintro ⟨h, hpr⟩
      exact hkk (hpr.pow_inj' hp0 (mem_Ioc.1 hk).1.ne' hk0.ne' h).2
  · rw [ite_eq_right hpp]
    symm
    apply sum_eq_zero; intro k hk
    apply sum_eq_zero; intro p _
    rw [ite_eq_right]
    rintro ⟨h, hpr⟩
    exact hpp ⟨p, k, Nat.prime_iff.1 hpr, (mem_Ioc.1 hk).1, h⟩

/-- `∑_{n ≤ x, n = q^e prime power} w(e) = ∑_{1 ≤ e ≤ x} w(e) · #{q prime : q^e ≤ x}`. -/
theorem sum_primePow_weight (w : ℕ → ℤ) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if IsPrimePow n then w (Ω n) else 0)
      = ∑ k ∈ Ioc 0 x, w k * (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ) := by
  rw [sum_congr rfl fun n hn => ppow_pointwise_w w hn, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_comm]
  have : ∀ p ∈ Ioc 0 x, ∑ n ∈ Ioc 0 x, (if p ^ k = n ∧ p.Prime then w k else 0)
      = if p.Prime ∧ p ^ k ≤ x then w k else 0 := by
    intro p hp
    simp only [ite_and]
    rw [sum_ite_eq]
    have hp0 : 0 < p := (mem_Ioc.1 hp).1
    have hpk : 0 < p ^ k := pow_pos hp0 k
    by_cases hpr : p.Prime <;> by_cases hle : p ^ k ≤ x <;> simp [hpr, hle, mem_Ioc, hpk]
  rw [sum_congr rfl this, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- `G(x) = ∑_{1 ≤ e ≤ x} e · #{q prime : q^e ≤ x}`, i.e. `∑_e e π(⌊x^(1/e)⌋)`. -/
theorem Gpp_eq_sum_prime_counts (x : ℕ) :
    Gpp x = ∑ k ∈ Ioc 0 x, (k : ℤ) * (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ) :=
  sum_primePow_weight (fun k => (k : ℤ)) x

/-- The `e = 1` count is the prime-counting function `π(x)`. -/
theorem prime_count_one (x : ℕ) :
    ((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ 1 ≤ x)).card = Nat.primeCounting x := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, pow_one, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, h⟩, hp, _⟩; exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, h⟩, hp, h⟩

/-- **Prime counts mod 3 from cyclic-orbit counts.** For `x ≥ 1`,
`π(x) + ∑_{2 ≤ e ≤ x} e · #{q prime : q^e ≤ x} ≡ ∑_{c ≤ x^(1/3)} μ(c) H(⌊x/c^3⌋) (mod 3)`. -/
theorem primeCounting_mod_three {x : ℕ} (hx : 1 ≤ x) :
    (Nat.primeCounting x : ℤ)
        + ∑ k ∈ Ioc 1 x, (k : ℤ) * (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ)
      ≡ ∑ c ∈ Icc 1 (icbrt x), μ c * (H (x / c ^ 3) : ℤ) [ZMOD 3] := by
  have h := G_mod_three hx
  rw [Gpp_eq_sum_prime_counts] at h
  have hsplit : Ioc 0 x = insert 1 (Ioc 1 x) := by
    ext k; simp only [mem_Ioc, mem_insert]; omega
  have hs : ∀ F : ℕ → ℤ, ∑ k ∈ Ioc 0 x, F k = F 1 + ∑ k ∈ Ioc 1 x, F k := by
    intro F; rw [hsplit, sum_insert (by simp)]
  rw [hs (fun k => (k : ℤ) * (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ)),
    prime_count_one] at h
  simpa using h

end M2L3
