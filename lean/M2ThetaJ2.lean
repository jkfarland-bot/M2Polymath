module

public import Mathlib
public import M2ThetaJ

/-!
  Seat M2L4, item 5a: Theorem J (A19 section 13) beyond round 3: a general slice form covering
  rational combinations with denominators 2^e 3^t (in particular 3-power denominators and the
  half-integral case thetaJ_half, restated here), and the principal split prime variant
  (base 2 only). The theta-series facts remain hypotheses, as in round 3.
-/

@[expose] public section

open ArithmeticFunction Finset

namespace M2L4
open M2L3

/-- **Slice form of Theorem J.** `S` an infinite set of primes; on every product of `r` distinct
primes of `S` (`r ≥ 1`), `2^e 3^t θ = A 2^r + B (-1)^r` for fixed integers `A, B`. Then for every
correction `h` vanishing on squarefree `n > 1`, `θ * h` cannot be nonzero mod `3^m` at every prime
of `S` while vanishing mod `3^m` on every product of at least two distinct primes of `S`. -/
theorem thetaJ_slice (m e t : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (theta : ArithmeticFunction ℤ) (A B : ℤ)
    (hval : ∀ s : Finset ℕ, ↑s ⊆ S → 1 ≤ s.card →
      2 ^ e * 3 ^ t * theta (∏ p ∈ s, p) = A * 2 ^ s.card + B * (-1) ^ s.card)
    (h : ArithmeticFunction ℤ) (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ (theta * h) q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ (theta * h) (∏ p ∈ s, p))) := by
  rintro ⟨hprime, hcomp⟩
  obtain ⟨s, hsS, hcard⟩ := hinf.exists_subset_card_eq (1 + 2 * 3 ^ (m + t))
  have hs_pr : ∀ p ∈ s, p.Prime := fun p hp => hS p (hsS hp)
  obtain ⟨q, hq⟩ : s.Nonempty := by rw [← card_pos, hcard]; positivity
  have hqS : q ∈ S := hsS hq
  have hq1 : ↑({q} : Finset ℕ) ⊆ S := by simpa using hqS
  have vq := hval {q} hq1 (by simp)
  simp only [prod_singleton, card_singleton, pow_one] at vq
  have vS := hval s hsS (by rw [hcard]; omega)
  rw [hcard] at vS
  have hodd : Odd (1 + 2 * 3 ^ (m + t)) := ⟨3 ^ (m + t), by ring⟩
  rw [hodd.neg_one_pow] at vS
  -- `θ` agrees on `q` and on `∏ s` modulo `3^m`
  have hd : (3 : ℤ) ^ (m + t + 1) ∣ 2 ^ (1 + 2 * 3 ^ (m + t)) - 2 := (two_pow_cong (m + t)).symm.dvd
  have key : (3 : ℤ) ^ m * 3 ^ t ∣ 2 ^ e * (theta (∏ p ∈ s, p) - theta q) * 3 ^ t := by
    have e1 : 2 ^ e * (theta (∏ p ∈ s, p) - theta q) * 3 ^ t
        = A * (2 ^ (1 + 2 * 3 ^ (m + t)) - 2) := by linear_combination vS - vq
    rw [e1, ← pow_add]
    exact Dvd.dvd.mul_left ((pow_dvd_pow 3 (by omega)).trans hd) _
  have k2 : (3 : ℤ) ^ m ∣ 2 ^ e * (theta (∏ p ∈ s, p) - theta q) :=
    Int.dvd_of_mul_dvd_mul_right (pow_ne_zero _ (by norm_num)) key
  have hcop : IsCoprime ((3 : ℤ) ^ m) (2 ^ e) := IsCoprime.pow ⟨1, -1, by norm_num⟩
  have k3 : (3 : ℤ) ^ m ∣ theta (∏ p ∈ s, p) - theta q := hcop.dvd_of_dvd_mul_left k2
  -- the filter on the squarefree arguments
  have hFS := mul_corr_squarefree theta h hh (squarefree_prod_primes hs_pr)
  have hFq := mul_corr_squarefree theta h hh (Nat.prime_iff.1 (hS q hqS)).squarefree
  have hdS := hcomp s hsS (by rw [hcard]; have := Nat.one_le_pow (m + t) 3 (by norm_num); omega)
  apply hprime q hqS
  rw [hFq]
  rw [hFS] at hdS
  have := dvd_sub hdS (k3.mul_left (h 1))
  rwa [show h 1 * theta (∏ p ∈ s, p) - h 1 * (theta (∏ p ∈ s, p) - theta q) = h 1 * theta q by ring]
    at this

/-- **Theorem J with 3-power denominators**: `2 · 3^t θ = c_0 r_0 + c_1 r_1` (any `t`), at the
nonprincipal split primes (`(a_0, a_ψ) = (2^r, (-1)^r)` on products of `r` of them). -/
theorem thetaJ_denominator (m t : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (r0 r1 a0 apsi : ArithmeticFunction ℤ)
    (hT1 : ∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n)
    (hval : ∀ s : Finset ℕ, ↑s ⊆ S →
      a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = (-1) ^ s.card)
    (c0 c1 : ℤ) (theta : ArithmeticFunction ℤ)
    (htheta : ∀ n, 2 * 3 ^ t * theta n = c0 * r0 n + c1 * r1 n)
    (h : ArithmeticFunction ℤ) (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ (theta * h) q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ (theta * h) (∏ p ∈ s, p))) := by
  refine thetaJ_slice m 0 (t + 1) S hS hinf theta (c0 + c1) (2 * c0 - c1) (fun s hs _ => ?_) h hh
  have v := thetaJ_value c0 c1 _ _ _ _ s.card (hT1 (∏ p ∈ s, p)).1 (hT1 (∏ p ∈ s, p)).2
    (hval s hs).1 (hval s hs).2
  have ht := htheta (∏ p ∈ s, p)
  rw [pow_zero, one_mul, pow_succ]
  have h2 : (2 : ℤ) * (3 ^ t * 3 * theta (∏ p ∈ s, p))
      = 2 * ((c0 + c1) * 2 ^ s.card + (2 * c0 - c1) * (-1) ^ s.card) := by
    linear_combination 3 * ht + v
  exact mul_left_cancel₀ (by norm_num) h2

/-- **thetaJ_half** (audit M2L3-v), restated: half-integral combinations `2 θ = c_0 r_0 + c_1 r_1`. -/
theorem thetaJ_half (m : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (r0 r1 a0 apsi : ArithmeticFunction ℤ)
    (hT1 : ∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n)
    (hval : ∀ s : Finset ℕ, ↑s ⊆ S →
      a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = (-1) ^ s.card)
    (c0 c1 : ℤ) (theta : ArithmeticFunction ℤ) (htheta : ∀ n, 2 * theta n = c0 * r0 n + c1 * r1 n)
    (h : ArithmeticFunction ℤ) (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ (theta * h) q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ (theta * h) (∏ p ∈ s, p))) :=
  thetaJ_denominator m 0 S hS hinf r0 r1 a0 apsi hT1 hval c0 c1 theta
    (fun n => by rw [pow_zero, mul_one]; exact htheta n) h hh

/-- **Principal split variant**: at principal split primes `a_0 = a_ψ = 2` (both classes see the
trivial character), so on a product of `r` of them `(a_0, a_ψ) = (2^r, 2^r)`: only the base `2`.
No combination `2 · 3^t θ = c_0 r_0 + c_1 r_1` gives a filter there either. -/
theorem thetaJ_principal (m t : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (r0 r1 a0 apsi : ArithmeticFunction ℤ)
    (hT1 : ∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n)
    (hval : ∀ s : Finset ℕ, ↑s ⊆ S →
      a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = 2 ^ s.card)
    (c0 c1 : ℤ) (theta : ArithmeticFunction ℤ)
    (htheta : ∀ n, 2 * 3 ^ t * theta n = c0 * r0 n + c1 * r1 n)
    (h : ArithmeticFunction ℤ) (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ (theta * h) q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ (theta * h) (∏ p ∈ s, p))) := by
  refine thetaJ_slice m 0 t S hS hinf theta c0 0 (fun s hs _ => ?_) h hh
  obtain ⟨h0, hpsi⟩ := hval s hs
  obtain ⟨e1, e2⟩ := hT1 (∏ p ∈ s, p)
  have ht := htheta (∏ p ∈ s, p)
  rw [h0] at e2; rw [hpsi] at e1
  -- `r_1 = 0` and `r_0 = 2 · 2^r` on this slice
  have hr1 : r1 (∏ p ∈ s, p) = 0 := by linarith
  have hr0 : r0 (∏ p ∈ s, p) = 2 * 2 ^ s.card := by linarith
  rw [hr1, hr0] at ht
  rw [pow_zero, one_mul, zero_mul, add_zero]
  linarith

/-- Non-vacuity of the principal-variant hypotheses: `S` = all primes, `a_0 = a_ψ = 2^ω`,
`r_1 = 0`, `r_0 = 2 · 2^ω`. -/
theorem thetaJ_principal_hyps_consistent :
    ∃ (S : Set ℕ) (r0 r1 a0 apsi : ArithmeticFunction ℤ),
      (∀ q ∈ S, q.Prime) ∧ S.Infinite ∧
      (∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S →
        a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = 2 ^ s.card) := by
  let r0 : ArithmeticFunction ℤ := ⟨fun n => 2 * powOmega 2 n, by simp⟩
  refine ⟨{p | p.Prime}, r0, 0, powOmega 2, powOmega 2, fun q hq => hq,
    Nat.infinite_setOfPred_prime, fun n => ?_, fun s hs => ?_⟩
  · have : r0 n = 2 * powOmega 2 n := rfl
    simp [this]
  · have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs hp
    exact ⟨powOmega_prod 2 hs', powOmega_prod 2 hs'⟩

end M2L4
