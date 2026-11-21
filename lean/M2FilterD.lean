module

public import Mathlib
public import M2Polymath

/-!
  Seat M2L3, item 3: A19 Theorem D (section 5), the two explicit filters.
  Mod 9: A(q^e) = 1 + q^2 + q^4, B(q^e) = A(q^e) for q ≠ 3, B(3^e) = 0, F = 3A - 2B.
  Mod 4: A(q^e) = 1 + q^2, B(q^e) = A(q^e) for odd q, B(2^e) = 0, F = 2A - B.
  Pointwise: F(1) = 1, F(q^e) ≡ 3 (mod 9) (resp. 2 mod 4), F(n) ≡ 0 when ω(n) ≥ 2; summed (D3), (D2).
  Model: A = G_A * h_A, B = G_B * h_B with G the products of ℓ(χ, k) and h multiplicative,
  zero at every prime, supported on squarefull integers.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.Moebius
  ArithmeticFunction.omega ArithmeticFunction.Omega

namespace M2L3

/-! ## The local facts -/

/-- `1 + q^2 + q^4 ≡ 3 (mod 9)` for every integer `q` not divisible by 3. -/
theorem local_mod9 (q : ℤ) (hq : ¬ (3 : ℤ) ∣ q) : 1 + q ^ 2 + q ^ 4 ≡ 3 [ZMOD 9] := by
  have h9 : q % 9 < 9 := Int.emod_lt_of_pos q (by norm_num)
  have h0 : 0 ≤ q % 9 := Int.emod_nonneg q (by norm_num)
  have hq' : q % 9 ≠ 0 ∧ q % 9 ≠ 3 ∧ q % 9 ≠ 6 := by omega
  have hm : q ≡ q % 9 [ZMOD 9] := (Int.mod_modEq q 9).symm
  have e := ((Int.ModEq.refl (1 : ℤ)).add (hm.pow 2)).add (hm.pow 4)
  refine e.trans ?_
  interval_cases hr : q % 9 <;> simp_all <;> decide

/-- `1 + q^2 ≡ 2 (mod 4)` for every odd integer `q`. -/
theorem local_mod4 (q : ℤ) (hq : ¬ (2 : ℤ) ∣ q) : 1 + q ^ 2 ≡ 2 [ZMOD 4] := by
  have h4 : q % 4 < 4 := Int.emod_lt_of_pos q (by norm_num)
  have h0 : 0 ≤ q % 4 := Int.emod_nonneg q (by norm_num)
  have hq' : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hm : q ≡ q % 4 [ZMOD 4] := (Int.mod_modEq q 4).symm
  refine ((Int.ModEq.refl (1 : ℤ)).add (hm.pow 2)).trans ?_
  rcases hq' with h | h <;> rw [h] <;> decide

/-! ## A generic two-core filter `F = r A - (r - 1) B` -/

section Generic

variable (r : ℕ) (g : ℕ → ℤ)

/-- `A = ∏_{p | n} g(p)`: the multiplicative function with `A(q^e) = g(q)` for `e ≥ 1`. -/
def Afun : ArithmeticFunction ℤ := prodPrimeFactors g

/-- `B = ∏_{p | n} (g(p) if p ≠ r, 0 if p = r)`. -/
def Bfun : ArithmeticFunction ℤ := prodPrimeFactors (fun p => if p = r then 0 else g p)

/-- The filter `F(n) = r A(n) - (r - 1) B(n)`. -/
def Ffun (n : ℕ) : ℤ := (r : ℤ) * Afun g n - ((r : ℤ) - 1) * Bfun r g n

lemma Afun_prime_pow {q e : ℕ} (hq : q.Prime) (he : 0 < e) : Afun g (q ^ e) = g q := by
  rw [Afun, prodPrimeFactors_apply (pow_ne_zero _ hq.ne_zero),
    Nat.primeFactors_prime_pow he.ne' hq, prod_singleton]

lemma Bfun_prime_pow {q e : ℕ} (hq : q.Prime) (he : 0 < e) :
    Bfun r g (q ^ e) = if q = r then 0 else g q := by
  rw [Bfun, prodPrimeFactors_apply (pow_ne_zero _ hq.ne_zero),
    Nat.primeFactors_prime_pow he.ne' hq, prod_singleton]

lemma Ffun_one : Ffun r g 1 = 1 := by
  simp [Ffun, Afun, Bfun]

lemma Ffun_prime_pow_ne {q e : ℕ} (hq : q.Prime) (he : 0 < e) (hqr : q ≠ r) :
    Ffun r g (q ^ e) = g q := by
  rw [Ffun, Afun_prime_pow g hq he, Bfun_prime_pow r g hq he, ite_eq_right hqr]; ring

lemma Ffun_prime_pow_eq {e : ℕ} (hr : r.Prime) (he : 0 < e) :
    Ffun r g (r ^ e) = r * g r := by
  rw [Ffun, Afun_prime_pow g hr he, Bfun_prime_pow r g hr he, ite_eq_left rfl]; ring

/-- If `r ∣ g(p)` for every prime `p ≠ r`, then `r^2 ∣ F(n)` whenever `ω(n) ≥ 2`. -/
theorem Ffun_dvd (hg : ∀ p, p.Prime → p ≠ r → (r : ℤ) ∣ g p)
    {n : ℕ} (hn : 2 ≤ ω n) : (r : ℤ) ^ 2 ∣ Ffun r g n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hcard : 2 ≤ n.primeFactors.card := by rw [card_primeFactors_eq_omega]; exact hn
  unfold Ffun Afun Bfun
  rw [prodPrimeFactors_apply hn0, prodPrimeFactors_apply hn0]
  by_cases hrn : r ∈ n.primeFactors
  · -- B(n) = 0 and some other prime `p ≠ r` divides `n`
    rw [prod_eq_zero (f := fun p => if p = r then (0 : ℤ) else g p) hrn (by simp), mul_zero,
      sub_zero, sq]
    obtain ⟨p, hp, hpr⟩ : ∃ p ∈ n.primeFactors, p ≠ r := by
      by_contra h
      push Not at h
      have : n.primeFactors ⊆ {r} := fun p hp => mem_singleton.2 (h p hp)
      have := card_le_card this
      simp at this; omega
    exact mul_dvd_mul_left _ ((hg p (Nat.prime_of_mem_primeFactors hp) hpr).trans
      (dvd_prod_of_mem _ hp))
  · -- A(n) = B(n) and every factor is divisible by `r`
    have hAB : ∏ p ∈ n.primeFactors, (if p = r then 0 else g p) = ∏ p ∈ n.primeFactors, g p :=
      prod_congr rfl fun p hp => ite_eq_right (fun (h : p = r) => hrn (h ▸ hp))
    rw [hAB, show (r : ℤ) * ∏ p ∈ n.primeFactors, g p - ((r : ℤ) - 1) * ∏ p ∈ n.primeFactors, g p
      = ∏ p ∈ n.primeFactors, g p by ring]
    have hd : ∏ _p ∈ n.primeFactors, (r : ℤ) ∣ ∏ p ∈ n.primeFactors, g p :=
      prod_dvd_prod_of_dvd _ _ fun p hp =>
        hg p (Nat.prime_of_mem_primeFactors hp) (fun (h : p = r) => hrn (h ▸ hp))
    rw [prod_const] at hd
    exact (pow_dvd_pow _ hcard).trans hd

/-- Summed form: if `F(q^e) ≡ r (mod r^2)` at every prime power, then for `x ≥ 1`
`∑_{n ≤ x} F(n) ≡ 1 + r · #{prime powers ≤ x} (mod r^2)`. -/
theorem Ffun_sum (hg : ∀ p, p.Prime → p ≠ r → (r : ℤ) ∣ g p)
    (hpp : ∀ q e, q.Prime → 0 < e → Ffun r g (q ^ e) ≡ r [ZMOD (r : ℤ) ^ 2])
    {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, Ffun r g n
      ≡ 1 + r * ∑ n ∈ Ioc 0 x, (if IsPrimePow n then (1 : ℤ) else 0) [ZMOD (r : ℤ) ^ 2] := by
  have key : (1 : ℤ) + r * ∑ n ∈ Ioc 0 x, (if IsPrimePow n then (1 : ℤ) else 0)
      = ∑ n ∈ Ioc 0 x, ((if n = 1 then (1 : ℤ) else 0)
          + r * (if IsPrimePow n then (1 : ℤ) else 0)) := by
    rw [sum_add_distrib, ← mul_sum, sum_ite_eq']; simp [hx]
  rw [key, Int.modEq_iff_dvd, ← sum_sub_distrib]
  apply dvd_sum
  intro n hn
  rw [← Int.modEq_iff_dvd]
  by_cases hn1 : n = 1
  · subst hn1; simp [Ffun_one, not_isPrimePow_one]
  rw [ite_eq_right hn1]
  by_cases hp : IsPrimePow n
  · obtain ⟨q, e, hq, he, rfl⟩ := hp
    rw [← Nat.prime_iff] at hq
    rw [ite_eq_left ⟨q, e, Nat.prime_iff.1 hq, he, rfl⟩]
    simpa using hpp q e hq he
  · rw [ite_eq_right hp]
    have h2 : 2 ≤ ω n := by
      have h0 : ω n ≠ 0 := by rw [Ne, cardDistinctFactors_eq_zero]; have := (mem_Ioc.1 hn).1; omega
      have h1' : ω n ≠ 1 := fun h => hp (cardDistinctFactors_eq_one_iff.1 h)
      omega
    simpa [Int.modEq_iff_dvd] using (Ffun_dvd r g hg h2)

end Generic

/-! ## Instances: Theorem D mod 9 and mod 4 -/

/-- `g_9(q) = 1 + q^2 + q^4`, the prime value of `ℓ(1,0) * ℓ(1,2) * ℓ(1,4)`. -/
def g9 (q : ℕ) : ℤ := 1 + (q : ℤ) ^ 2 + (q : ℤ) ^ 4

/-- `g_4(q) = 1 + q^2`, the prime value of `ℓ(1,0) * ℓ(1,2)`. -/
def g4 (q : ℕ) : ℤ := 1 + (q : ℤ) ^ 2

/-- The mod 9 filter `F = 3A - 2B`. -/
abbrev F9 : ℕ → ℤ := Ffun 3 g9
/-- The mod 4 filter `F = 2A - B`. -/
abbrev F4 : ℕ → ℤ := Ffun 2 g4

lemma g9_dvd (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) : ((3 : ℕ) : ℤ) ∣ g9 p := by
  have hnd : ¬ (3 : ℤ) ∣ (p : ℤ) := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h).symm
  have := local_mod9 p hnd
  have h3 := Int.ModEq.of_mul_left 3 (show 1 + (p : ℤ) ^ 2 + (p : ℤ) ^ 4 ≡ 3 [ZMOD 3 * 3] from this)
  have := (Int.modEq_iff_dvd.1 h3)
  rw [g9]; push_cast
  have : (3 : ℤ) ∣ 1 + (p : ℤ) ^ 2 + (p : ℤ) ^ 4 := by
    have := Int.ModEq.dvd h3.symm
    simpa using this
  exact this

lemma g4_dvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ((2 : ℕ) : ℤ) ∣ g4 p := by
  have hnd : ¬ (2 : ℤ) ∣ (p : ℤ) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 h).symm
  have h2 := Int.ModEq.of_mul_left 2 (show 1 + (p : ℤ) ^ 2 ≡ 2 [ZMOD 2 * 2] from local_mod4 p hnd)
  rw [g4]; push_cast
  simpa using Int.ModEq.dvd h2.symm

/-- **Theorem D, mod 9, pointwise.** `F = 3A - 2B` with `A(q^e) = 1 + q^2 + q^4`,
`B(q^e) = A(q^e)` for `q ≠ 3`, `B(3^e) = 0`:
`F(1) = 1`; `F(q^e) ≡ 3 (mod 9)` for every prime power; `F(3^e) = 273`;
`F(n) ≡ 0 (mod 9)` whenever `ω(n) ≥ 2`. -/
theorem thmD_mod9 :
    F9 1 = 1 ∧
    (∀ q e, q.Prime → 0 < e → F9 (q ^ e) ≡ 3 [ZMOD 9]) ∧
    (∀ e, 0 < e → F9 (3 ^ e) = 273) ∧
    (∀ n, 2 ≤ ω n → F9 n ≡ 0 [ZMOD 9]) := by
  have h273 : ∀ e, 0 < e → F9 (3 ^ e) = 273 := by
    intro e he
    rw [F9, Ffun_prime_pow_eq 3 g9 Nat.prime_three he, g9]; norm_num
  refine ⟨Ffun_one 3 g9, ?_, h273, ?_⟩
  · intro q e hq he
    by_cases hq3 : q = 3
    · subst hq3; rw [h273 e he]; decide
    · rw [F9, Ffun_prime_pow_ne 3 g9 hq he hq3, g9]
      apply local_mod9
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]
      intro h
      exact hq3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).1 h).symm
  · intro n hn
    have := Ffun_dvd 3 g9 g9_dvd hn
    rw [Int.modEq_zero_iff_dvd]
    simpa using this

/-- **Theorem D, mod 4, pointwise.** `F = 2A - B` with `A(q^e) = 1 + q^2`, `B(q^e) = A(q^e)` for
odd `q`, `B(2^e) = 0`: `F(1) = 1`; `F(q^e) ≡ 2 (mod 4)`; `F(2^e) = 10`; `F(n) ≡ 0 (mod 4)` when
`ω(n) ≥ 2`. -/
theorem thmD_mod4 :
    F4 1 = 1 ∧
    (∀ q e, q.Prime → 0 < e → F4 (q ^ e) ≡ 2 [ZMOD 4]) ∧
    (∀ e, 0 < e → F4 (2 ^ e) = 10) ∧
    (∀ n, 2 ≤ ω n → F4 n ≡ 0 [ZMOD 4]) := by
  have h10 : ∀ e, 0 < e → F4 (2 ^ e) = 10 := by
    intro e he
    rw [F4, Ffun_prime_pow_eq 2 g4 Nat.prime_two he, g4]; norm_num
  refine ⟨Ffun_one 2 g4, ?_, h10, ?_⟩
  · intro q e hq he
    by_cases hq2 : q = 2
    · subst hq2; rw [h10 e he]; decide
    · rw [F4, Ffun_prime_pow_ne 2 g4 hq he hq2, g4]
      apply local_mod4
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast]
      intro h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).1 h).symm
  · intro n hn
    have := Ffun_dvd 2 g4 g4_dvd hn
    rw [Int.modEq_zero_iff_dvd]
    simpa using this

/-- The number of prime powers up to `x` is `∑_{j ≥ 1} π(⌊x^(1/j)⌋)`. -/
theorem card_primePow_eq (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if IsPrimePow n then (1 : ℤ) else 0)
      = ∑ k ∈ Ioc 0 x, (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ) := by
  simpa using sum_primePow_weight (fun _ => (1 : ℤ)) x

/-- **(D3)**: for `x ≥ 1`, `∑_{n ≤ x} F(n) ≡ 1 + 3 ∑_{j ≥ 1} π(⌊x^(1/j)⌋) (mod 9)`. -/
theorem thmD_D3 {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, F9 n ≡ 1 + 3 * ∑ k ∈ Ioc 0 x,
      (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ) [ZMOD 9] := by
  rw [← card_primePow_eq]
  have := Ffun_sum 3 g9 g9_dvd
    (fun q e hq he => by simpa using thmD_mod9.2.1 q e hq he) hx
  simpa using this

/-- **(D2)**: for `x ≥ 1`, `∑_{n ≤ x} F(n) ≡ 1 + 2 ∑_{j ≥ 1} π(⌊x^(1/j)⌋) (mod 4)`. -/
theorem thmD_D2 {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, F4 n ≡ 1 + 2 * ∑ k ∈ Ioc 0 x,
      (((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x)).card : ℤ) [ZMOD 4] := by
  rw [← card_primePow_eq]
  have := Ffun_sum 2 g4 g4_dvd
    (fun q e hq he => by simpa using thmD_mod4.2.1 q e hq he) hx
  simpa using this

/-! ## The model: `A = G_A * h_A`, `B = G_B * h_B` with squarefull corrections -/

/-- `ℓ(1, k)(n) = n^k` (trivial character). -/
def ellOne (k : ℕ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else (n : ℤ) ^ k, by simp⟩

/-- `ℓ(χ_{0,r}, k)(n) = χ_{0,r}(n) n^k` with `χ_{0,r}` the principal character modulo `r`. -/
def ellPrin (r k : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 ∨ r ∣ n then 0 else (n : ℤ) ^ k, by simp⟩

lemma ellOne_apply (k n : ℕ) : ellOne k n = if n = 0 then 0 else (n : ℤ) ^ k := rfl
lemma ellPrin_apply (r k n : ℕ) : ellPrin r k n = if n = 0 ∨ r ∣ n then 0 else (n : ℤ) ^ k := rfl

lemma ellOne_cmul (k a b : ℕ) : ellOne k (a * b) = ellOne k a * ellOne k b := by
  simp only [ellOne_apply, mul_eq_zero]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, mul_pow]

lemma ellPrin_cmul {r : ℕ} (hr : r.Prime) (k a b : ℕ) :
    ellPrin r k (a * b) = ellPrin r k a * ellPrin r k b := by
  simp only [ellPrin_apply, mul_eq_zero, hr.dvd_mul]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hra : r ∣ a <;>
    by_cases hrb : r ∣ b <;> simp [ha, hb, hra, hrb, mul_pow]

lemma isMult_of_cmul {f : ArithmeticFunction ℤ} (h1 : f 1 = 1)
    (h : ∀ a b, f (a * b) = f a * f b) : IsMultiplicative f :=
  ⟨h1, fun {_ _} _ => h _ _⟩

/-- A completely multiplicative `ℓ` has Dirichlet inverse `ℓ · μ`. -/
lemma cmul_inverse {f : ArithmeticFunction ℤ} (h1 : f 1 = 1) (h : ∀ a b, f (a * b) = f a * f b) :
    f * f.pmul (μ : ArithmeticFunction ℤ) = 1 := by
  ext n
  rw [mul_apply]
  have : ∀ x ∈ n.divisorsAntidiagonal, f x.1 * (f.pmul (μ : ArithmeticFunction ℤ)) x.2
      = f n * ((ζ : ArithmeticFunction ℤ) x.1 * (μ : ArithmeticFunction ℤ) x.2) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hx1 : x.1 ≠ 0 := by rintro h0; rw [h0, zero_mul] at hx; exact hx.2 hx.1.symm
    rw [pmul_apply, ← hx.1, h, natCoe_apply, zeta_apply, ite_eq_right hx1]
    push_cast; ring
  rw [sum_congr rfl this, ← mul_sum, ← mul_apply, coe_zeta_mul_moebius, one_apply]
  split_ifs with hn
  · rw [hn, h1, mul_one]
  · rw [mul_zero]

/-- For multiplicative `f, g` and a prime `q`: `(f * g)(q) = f(q) + g(q)`. -/
lemma mul_apply_prime {f g : ArithmeticFunction ℤ} (hf : IsMultiplicative f)
    (hg : IsMultiplicative g) {q : ℕ} (hq : q.Prime) : (f * g) q = f q + g q := by
  have := mul_apply_prime_pow f g hq 1
  rw [pow_one] at this
  rw [this, sum_range_succ, sum_range_one]
  simp [hf.map_one, hg.map_one, add_comm]

/-- A multiplicative function vanishing at every prime is supported on squarefull integers. -/
lemma squarefull_of_prime_zero {h : ArithmeticFunction ℤ} (hh : IsMultiplicative h)
    (hq : ∀ q, q.Prime → h q = 0) {n : ℕ} (hn : h n ≠ 0) :
    ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n := by
  intro p hp hpn
  by_contra hsq
  obtain ⟨m, rfl⟩ := hpn
  have hpm : ¬ p ∣ m := fun hd => hsq (by rw [sq]; exact Nat.mul_dvd_mul_left p hd)
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  apply hn
  rw [hh.map_mul_of_coprime hcop, hq p hp, zero_mul]

/-- **Theorem C's correction for a fixed core**: if `G * G⁻¹ = 1` (both multiplicative) and `T` is
multiplicative with `T(q) = G(q)` at every prime, then `h = T * G⁻¹` is multiplicative, `G * h = T`,
`h(q) = 0` at every prime, and `h` is supported on squarefull integers. -/
theorem correction (G Gi T : ArithmeticFunction ℤ) (hG : IsMultiplicative G)
    (hGi : IsMultiplicative Gi) (hT : IsMultiplicative T) (hinv : G * Gi = 1)
    (hprime : ∀ q, q.Prime → T q = G q) :
    IsMultiplicative (T * Gi) ∧ G * (T * Gi) = T ∧ (∀ q, q.Prime → (T * Gi) q = 0) ∧
      (∀ n, (T * Gi) n ≠ 0 → ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n) := by
  have hh : IsMultiplicative (T * Gi) := hT.mul hGi
  have hzero : ∀ q, q.Prime → (T * Gi) q = 0 := by
    intro q hq
    have e1 := mul_apply_prime hG hGi hq
    rw [hinv, one_apply, ite_eq_right hq.one_lt.ne'] at e1
    rw [mul_apply_prime hT hGi hq, hprime q hq]
    linarith
  refine ⟨hh, ?_, hzero, fun n hn => squarefull_of_prime_zero hh hzero hn⟩
  rw [mul_left_comm, hinv, mul_one]

lemma ellOne_mult (k : ℕ) : IsMultiplicative (ellOne k) :=
  isMult_of_cmul (by simp [ellOne_apply]) (ellOne_cmul k)
lemma ellPrin_mult {r : ℕ} (hr : r.Prime) (k : ℕ) : IsMultiplicative (ellPrin r k) :=
  isMult_of_cmul (by simp [ellPrin_apply, hr.one_lt.ne', Nat.dvd_one]) (ellPrin_cmul hr k)

/-- `G_A = ℓ(1,0) * ℓ(1,2) * ℓ(1,4)`. -/
def GA9 : ArithmeticFunction ℤ := ellOne 0 * ellOne 2 * ellOne 4
/-- `G_B = ℓ(χ_{0,3},0) * ℓ(χ_{0,3},2) * ℓ(χ_{0,3},4)`. -/
def GB9 : ArithmeticFunction ℤ := ellPrin 3 0 * ellPrin 3 2 * ellPrin 3 4
/-- `G_A = ℓ(1,0) * ℓ(1,2)` (mod 4 case). -/
def GA4 : ArithmeticFunction ℤ := ellOne 0 * ellOne 2
/-- `G_B = ℓ(χ_{0,2},0) * ℓ(χ_{0,2},2)` (mod 4 case). -/
def GB4 : ArithmeticFunction ℤ := ellPrin 2 0 * ellPrin 2 2

/-- **Theorem D, the model (mod 9)**: `A = G_A * h_A` and `B = G_B * h_B` with `h_A`, `h_B`
multiplicative, zero at every prime, and supported on squarefull integers. -/
theorem thmD_model_mod9 :
    ∃ hA hB : ArithmeticFunction ℤ, GA9 * hA = Afun g9 ∧ GB9 * hB = Bfun 3 g9 ∧
      IsMultiplicative hA ∧ IsMultiplicative hB ∧
      (∀ q, q.Prime → hA q = 0 ∧ hB q = 0) ∧
      (∀ n, hA n ≠ 0 → ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n) ∧
      (∀ n, hB n ≠ 0 → ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n) := by
  have i0 := cmul_inverse (by simp [ellOne_apply]) (ellOne_cmul 0)
  have i2 := cmul_inverse (by simp [ellOne_apply]) (ellOne_cmul 2)
  have i4 := cmul_inverse (by simp [ellOne_apply]) (ellOne_cmul 4)
  have j0 := cmul_inverse (by simp [ellPrin_apply]) (ellPrin_cmul Nat.prime_three 0)
  have j2 := cmul_inverse (by simp [ellPrin_apply]) (ellPrin_cmul Nat.prime_three 2)
  have j4 := cmul_inverse (by simp [ellPrin_apply]) (ellPrin_cmul Nat.prime_three 4)
  have mo := isMultiplicative_moebius.intCast (R := ℤ)
  have hGA : IsMultiplicative GA9 := ((ellOne_mult 0).mul (ellOne_mult 2)).mul (ellOne_mult 4)
  have hGB : IsMultiplicative GB9 :=
    ((ellPrin_mult Nat.prime_three 0).mul (ellPrin_mult Nat.prime_three 2)).mul
      (ellPrin_mult Nat.prime_three 4)
  set IA := (ellOne 0).pmul (μ : ArithmeticFunction ℤ) * (ellOne 2).pmul (μ : ArithmeticFunction ℤ)
    * (ellOne 4).pmul (μ : ArithmeticFunction ℤ) with hIA
  set IB := (ellPrin 3 0).pmul (μ : ArithmeticFunction ℤ) * (ellPrin 3 2).pmul
    (μ : ArithmeticFunction ℤ) * (ellPrin 3 4).pmul (μ : ArithmeticFunction ℤ) with hIB
  have hIA' : IsMultiplicative IA :=
    (((ellOne_mult 0).pmul mo).mul ((ellOne_mult 2).pmul mo)).mul ((ellOne_mult 4).pmul mo)
  have hIB' : IsMultiplicative IB :=
    (((ellPrin_mult Nat.prime_three 0).pmul mo).mul ((ellPrin_mult Nat.prime_three 2).pmul mo)).mul
      ((ellPrin_mult Nat.prime_three 4).pmul mo)
  have invA : GA9 * IA = 1 := by
    rw [GA9, hIA]
    calc _ = (ellOne 0 * (ellOne 0).pmul (μ : ArithmeticFunction ℤ))
        * (ellOne 2 * (ellOne 2).pmul (μ : ArithmeticFunction ℤ))
        * (ellOne 4 * (ellOne 4).pmul (μ : ArithmeticFunction ℤ)) := by ring
      _ = 1 := by rw [i0, i2, i4]; ring
  have invB : GB9 * IB = 1 := by
    rw [GB9, hIB]
    calc _ = (ellPrin 3 0 * (ellPrin 3 0).pmul (μ : ArithmeticFunction ℤ))
        * (ellPrin 3 2 * (ellPrin 3 2).pmul (μ : ArithmeticFunction ℤ))
        * (ellPrin 3 4 * (ellPrin 3 4).pmul (μ : ArithmeticFunction ℤ)) := by ring
      _ = 1 := by rw [j0, j2, j4]; ring
  have pA : ∀ q, q.Prime → Afun g9 q = GA9 q := by
    intro q hq
    rw [GA9, mul_apply_prime ((ellOne_mult 0).mul (ellOne_mult 2)) (ellOne_mult 4) hq,
      mul_apply_prime (ellOne_mult 0) (ellOne_mult 2) hq, ← pow_one q, Afun_prime_pow g9 hq one_pos]
    simp [ellOne_apply, hq.ne_zero, g9]
  have pB : ∀ q, q.Prime → Bfun 3 g9 q = GB9 q := by
    intro q hq
    rw [GB9, mul_apply_prime ((ellPrin_mult Nat.prime_three 0).mul (ellPrin_mult Nat.prime_three 2))
      (ellPrin_mult Nat.prime_three 4) hq,
      mul_apply_prime (ellPrin_mult Nat.prime_three 0) (ellPrin_mult Nat.prime_three 2) hq,
      ← pow_one q, Bfun_prime_pow 3 g9 hq one_pos]
    have h3 : 3 ∣ q ↔ q = 3 := ⟨fun h => ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h).symm,
      fun h => h ▸ dvd_rfl⟩
    by_cases hq3 : q = 3
    · simp [ellPrin_apply, hq3]
    · simp [ellPrin_apply, hq.ne_zero, h3, hq3, g9]
  obtain ⟨mA, eA, zA, sA⟩ := correction GA9 IA (Afun g9) hGA hIA'
    (IsMultiplicative.prodPrimeFactors _) invA pA
  obtain ⟨mB, eB, zB, sB⟩ := correction GB9 IB (Bfun 3 g9) hGB hIB'
    (IsMultiplicative.prodPrimeFactors _) invB pB
  exact ⟨_, _, eA, eB, mA, mB, fun q hq => ⟨zA q hq, zB q hq⟩, sA, sB⟩

/-- **Theorem D, the model (mod 4)**: `A = G_A * h_A` and `B = G_B * h_B` with `h_A`, `h_B`
multiplicative, zero at every prime, and supported on squarefull integers. -/
theorem thmD_model_mod4 :
    ∃ hA hB : ArithmeticFunction ℤ, GA4 * hA = Afun g4 ∧ GB4 * hB = Bfun 2 g4 ∧
      IsMultiplicative hA ∧ IsMultiplicative hB ∧
      (∀ q, q.Prime → hA q = 0 ∧ hB q = 0) ∧
      (∀ n, hA n ≠ 0 → ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n) ∧
      (∀ n, hB n ≠ 0 → ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n) := by
  have i0 := cmul_inverse (by simp [ellOne_apply]) (ellOne_cmul 0)
  have i2 := cmul_inverse (by simp [ellOne_apply]) (ellOne_cmul 2)
  have j0 := cmul_inverse (by simp [ellPrin_apply]) (ellPrin_cmul Nat.prime_two 0)
  have j2 := cmul_inverse (by simp [ellPrin_apply]) (ellPrin_cmul Nat.prime_two 2)
  have mo := isMultiplicative_moebius.intCast (R := ℤ)
  have hGA : IsMultiplicative GA4 := (ellOne_mult 0).mul (ellOne_mult 2)
  have hGB : IsMultiplicative GB4 := (ellPrin_mult Nat.prime_two 0).mul (ellPrin_mult Nat.prime_two 2)
  set IA := (ellOne 0).pmul (μ : ArithmeticFunction ℤ) * (ellOne 2).pmul (μ : ArithmeticFunction ℤ)
    with hIA
  set IB := (ellPrin 2 0).pmul (μ : ArithmeticFunction ℤ) * (ellPrin 2 2).pmul
    (μ : ArithmeticFunction ℤ) with hIB
  have hIA' : IsMultiplicative IA := ((ellOne_mult 0).pmul mo).mul ((ellOne_mult 2).pmul mo)
  have hIB' : IsMultiplicative IB :=
    ((ellPrin_mult Nat.prime_two 0).pmul mo).mul ((ellPrin_mult Nat.prime_two 2).pmul mo)
  have invA : GA4 * IA = 1 := by
    rw [GA4, hIA]
    calc _ = (ellOne 0 * (ellOne 0).pmul (μ : ArithmeticFunction ℤ))
        * (ellOne 2 * (ellOne 2).pmul (μ : ArithmeticFunction ℤ)) := by ring
      _ = 1 := by rw [i0, i2]; ring
  have invB : GB4 * IB = 1 := by
    rw [GB4, hIB]
    calc _ = (ellPrin 2 0 * (ellPrin 2 0).pmul (μ : ArithmeticFunction ℤ))
        * (ellPrin 2 2 * (ellPrin 2 2).pmul (μ : ArithmeticFunction ℤ)) := by ring
      _ = 1 := by rw [j0, j2]; ring
  have pA : ∀ q, q.Prime → Afun g4 q = GA4 q := by
    intro q hq
    rw [GA4, mul_apply_prime (ellOne_mult 0) (ellOne_mult 2) hq, ← pow_one q,
      Afun_prime_pow g4 hq one_pos]
    simp [ellOne_apply, hq.ne_zero, g4]
  have pB : ∀ q, q.Prime → Bfun 2 g4 q = GB4 q := by
    intro q hq
    rw [GB4, mul_apply_prime (ellPrin_mult Nat.prime_two 0) (ellPrin_mult Nat.prime_two 2) hq,
      ← pow_one q, Bfun_prime_pow 2 g4 hq one_pos]
    have h2 : 2 ∣ q ↔ q = 2 := ⟨fun h => ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h).symm,
      fun h => h ▸ dvd_rfl⟩
    by_cases hq2 : q = 2
    · simp [ellPrin_apply, hq2]
    · simp [ellPrin_apply, hq.ne_zero, h2, hq2, g4]
  obtain ⟨mA, eA, zA, sA⟩ := correction GA4 IA (Afun g4) hGA hIA'
    (IsMultiplicative.prodPrimeFactors _) invA pA
  obtain ⟨mB, eB, zB, sB⟩ := correction GB4 IB (Bfun 2 g4) hGB hIB'
    (IsMultiplicative.prodPrimeFactors _) invB pB
  exact ⟨_, _, eA, eB, mA, mB, fun q hq => ⟨zA q hq, zB q hq⟩, sA, sB⟩

end M2L3
