module

public import Mathlib
public import M2ResultN

/-!
  Seat M2L4, item 7: the Frobenius identity for the Dirichlet ring,
  f^(*p) = E_p(Frob ∘ f) for every arithmetic function f over a commutative ring of
  characteristic p (p prime); over Z/p, f^(*p) = E_p(f); for integer-valued f,
  f^(*p) ≡ E_p(f) (mod p) coefficientwise.
-/

@[expose] public section

open ArithmeticFunction Finset

namespace M2L4

section Frob

variable {R : Type*} [CommRing R]

/-- `δ_d`: the indicator of `n = d` (for `d ≥ 1`). -/
def delta (d : ℕ) : ArithmeticFunction R := ⟨fun n => if n ≠ 0 ∧ n = d then 1 else 0, by simp⟩

lemma delta_apply (d n : ℕ) : (delta d : ArithmeticFunction R) n = if n ≠ 0 ∧ n = d then 1 else 0 :=
  rfl

lemma delta_mul (a b : ℕ) :
    (delta a : ArithmeticFunction R) * delta b = delta (a * b) := by
  ext n
  rw [mul_apply, delta_apply]
  by_cases h : n ≠ 0 ∧ n = a * b
  · rw [ite_eq_left h]
    have ha : a ≠ 0 := by rintro rfl; exact h.1 (by rw [h.2, zero_mul])
    have hb : b ≠ 0 := by rintro rfl; exact h.1 (by rw [h.2, mul_zero])
    rw [sum_eq_single_of_mem (a, b) (Nat.mem_divisorsAntidiagonal.2 ⟨h.2.symm, h.1⟩)]
    · simp [delta_apply, ha, hb]
    · intro x _ hx
      rw [delta_apply, delta_apply]
      by_cases h1 : x.1 ≠ 0 ∧ x.1 = a
      · by_cases h2 : x.2 ≠ 0 ∧ x.2 = b
        · exact absurd (Prod.ext h1.2 h2.2) hx
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
  · rw [ite_eq_right h]
    refine sum_eq_zero fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [delta_apply, delta_apply]
    by_cases h1 : x.1 ≠ 0 ∧ x.1 = a
    · by_cases h2 : x.2 ≠ 0 ∧ x.2 = b
      · exact absurd ⟨hx.2, by rw [← hx.1, h1.2, h2.2]⟩ h
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

lemma delta_one : (delta 1 : ArithmeticFunction R) = 1 := by
  ext n; rw [delta_apply, one_apply]
  by_cases h : n = 1
  · simp [h]
  · simp [h]

lemma delta_pow (d k : ℕ) : (delta d : ArithmeticFunction R) ^ k = delta (d ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, delta_one]
  | succ k ih => rw [pow_succ, ih, delta_mul, pow_succ]

/-- Powers of `f` at `n` depend only on the values of `f` at divisors of `n`. -/
lemma pow_apply_congr (f g : ArithmeticFunction R) (k : ℕ) :
    ∀ n, (∀ d, d ∣ n → f d = g d) → (f ^ k) n = (g ^ k) n := by
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n h
    rw [pow_succ', pow_succ', mul_apply, mul_apply]
    refine sum_congr rfl fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [h x.1 ⟨x.2, hx.1.symm⟩,
      ih x.2 (fun d hd => h d (hd.trans ⟨x.1, by rw [← hx.1, mul_comm]⟩))]

lemma sum_apply' {ι : Type*} (s : Finset ι) (F : ι → ArithmeticFunction R) (n : ℕ) :
    (∑ i ∈ s, F i) n = ∑ i ∈ s, F i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, ArithmeticFunction.add_apply, ih]

/-- The truncation `∑_{d ∣ n} f(d) δ_d`. -/
noncomputable def trunc (f : ArithmeticFunction R) (n : ℕ) : ArithmeticFunction R :=
  ∑ d ∈ n.divisors, f d • delta d

lemma trunc_apply (f : ArithmeticFunction R) {n m : ℕ} (hm : m ∣ n) (hn : n ≠ 0) :
    trunc f n m = f m := by
  rw [trunc, sum_apply']
  have hm0 : m ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hm)
  rw [sum_eq_single_of_mem m (Nat.mem_divisors.2 ⟨hm, hn⟩)]
  · show f m • (delta m : ArithmeticFunction R) m = f m
    rw [delta_apply, ite_eq_left ⟨hm0, rfl⟩, smul_eq_mul, mul_one]
  · intro d _ hd
    show f d • (delta d : ArithmeticFunction R) m = 0
    rw [delta_apply, ite_eq_right (fun h => hd h.2.symm), smul_zero]

/-- `Frob ∘ f`: `n ↦ f(n)^p`. -/
def frobF (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => f n ^ p, by simp [Nat.Prime.ne_zero Fact.out]⟩

instance charP_arith (p : ℕ) [CharP R p] : CharP (ArithmeticFunction R) p := by
  refine charP_of_injective_algebraMap (R := R) (fun x y h => ?_) p
  have := congrArg (fun F : ArithmeticFunction R => F 1) h
  simpa using this

/-- **Frobenius for the Dirichlet ring**: over a commutative ring of prime characteristic `p`,
`f^(*p) = E_p(Frob ∘ f)` for every arithmetic function `f`. -/
theorem frobenius_dirichlet (p : ℕ) [hp : Fact p.Prime] [CharP R p] (f : ArithmeticFunction R) :
    f ^ p = Ek p (frobF p f) := by
  have hp0 : 0 < p := hp.out.pos
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [pow_apply_congr f (trunc f n) p n (fun d hd => (trunc_apply f hd hn).symm), trunc,
    sum_pow_char]
  have e : ∀ d ∈ n.divisors, (f d • (delta d : ArithmeticFunction R)) ^ p
      = f d ^ p • delta (d ^ p) := by
    intro d _; rw [smul_pow, delta_pow]
  rw [sum_congr rfl e, sum_apply']
  have e2 : ∀ d ∈ n.divisors, (f d ^ p • (delta (d ^ p) : ArithmeticFunction R)) n
      = if d ^ p = n then f d ^ p else 0 := by
    intro d _
    show f d ^ p • (delta (d ^ p) : ArithmeticFunction R) n = _
    rw [delta_apply]
    by_cases h : d ^ p = n
    · rw [ite_eq_left ⟨hn, h.symm⟩, ite_eq_left h, smul_eq_mul, mul_one]
    · rw [ite_eq_right (fun h' => h h'.2.symm), ite_eq_right h, smul_zero]
  rw [sum_congr rfl e2]
  by_cases hpow : ∃ m, m ^ p = n
  · obtain ⟨m, rfl⟩ := hpow
    have hm : m ∈ (m ^ p).divisors := Nat.mem_divisors.2 ⟨dvd_pow_self m hp0.ne', hn⟩
    rw [sum_eq_single_of_mem m hm, ite_eq_left rfl, Ek_pow hp0]
    · rfl
    · intro d _ hd; rw [ite_eq_right (fun h => hd (pow_left_inj' hp0 h))]
  · rw [Ek_notpow _ (fun c hc => hpow ⟨c, hc⟩)]
    exact sum_eq_zero fun d _ => ite_eq_right (fun h => hpow ⟨d, h⟩)

end Frob

/-- **Over `ℤ/p`**: `f^(*p) = E_p(f)`, since `a^p = a` in `ℤ/p`. -/
theorem frobenius_zmod (p : ℕ) [hp : Fact p.Prime] (f : ArithmeticFunction (ZMod p)) :
    f ^ p = Ek p f := by
  rw [frobenius_dirichlet p f]
  congr 1
  ext n
  show f n ^ p = f n
  exact ZMod.pow_card _

/-- **For integer-valued `f`**: `f^(*p) ≡ E_p(f) (mod p)` at every `n`. -/
theorem frobenius_int (p : ℕ) [hp : Fact p.Prime] (f : ArithmeticFunction ℤ) (n : ℕ) :
    (f ^ p) n ≡ Ek p f n [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have h := congrArg (fun F : ArithmeticFunction (ZMod p) => F n)
    (frobenius_zmod p (f : ArithmeticFunction (ZMod p)))
  have hc : ∀ k : ℕ, ((f ^ k : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod p))
      = (f : ArithmeticFunction (ZMod p)) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, intCoe_one]
    | succ k ih => rw [pow_succ, pow_succ, intCoe_mul, ih]
  rw [← intCoe_apply, hc p, h, Ek_apply, Ek_apply]
  split_ifs <;> simp [intCoe_apply]

/-- Consistency with the cube case used for Result N: `ζ^(*3) = E_3(ζ)` over `ℤ/3`. -/
example : ζ3 ^ 3 = Ek 3 ζ3 := frobenius_zmod 3 ζ3

end M2L4
