/-
  Seat M2L3, item 4: the algebraic core of A19 Theorem J (section 13).
  The theta-series facts are hypotheses, stated plainly:
  (T1) a_ψ = (r_0 - r_1)/2, a_0 = (r_0 + 2 r_1)/2, and on a product of r distinct selected
  (nonprincipal split) primes, (a_0, a_ψ) = (2^r, (-1)^r).
  Conclusions: the value of c_0 r_0 + c_1 r_1 there is (2/3)[(c_0 + c_1) 2^r + (2 c_0 - c_1)(-1)^r];
  r = 1 and r = 1 + 2 * 3^m give the same value mod 3^m; hence no integral linear theta filter
  (with a correction vanishing on squarefree n > 1) separates the selected primes from their
  products, provided the selected primes form an infinite set (Chebotarev, a hypothesis here).
-/
import Mathlib

open ArithmeticFunction Finset

namespace M2L3

/-- **The value formula.** From (T1) and `(a_0, a_ψ) = (2^r, (-1)^r)`:
`3 (c_0 r_0 + c_1 r_1) = 2 [(c_0 + c_1) 2^r + (2 c_0 - c_1)(-1)^r]`. -/
theorem thetaJ_value (c0 c1 r0 r1 a0 apsi : ℤ) (r : ℕ)
    (hT1psi : 2 * apsi = r0 - r1) (hT1zero : 2 * a0 = r0 + 2 * r1)
    (h0 : a0 = 2 ^ r) (hpsi : apsi = (-1) ^ r) :
    3 * (c0 * r0 + c1 * r1) = 2 * ((c0 + c1) * 2 ^ r + (2 * c0 - c1) * (-1) ^ r) := by
  subst h0 hpsi
  linear_combination (-(2 * c0 - c1)) * hT1psi + (-(c0 + c1)) * hT1zero

/-- `2^(1 + 2 * 3^m) ≡ 2 (mod 3^(m+1))` (Euler, `φ(3^(m+1)) = 2 * 3^m`). -/
theorem two_pow_cong (m : ℕ) : (2 : ℤ) ^ (1 + 2 * 3 ^ m) ≡ 2 [ZMOD 3 ^ (m + 1)] := by
  have hcop : Nat.Coprime 2 (3 ^ (m + 1)) :=
    Nat.Coprime.pow_right _ (by norm_num)
  have he := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow_succ Nat.prime_three] at he
  have he' : (2 : ℤ) ^ (3 ^ m * 2) ≡ 1 [ZMOD 3 ^ (m + 1)] := by
    exact_mod_cast (Int.natCast_modEq_iff.2 he)
  rw [show (2 : ℤ) ^ (1 + 2 * 3 ^ m) = 2 * 2 ^ (3 ^ m * 2) by ring]
  have := (Int.ModEq.refl (2 : ℤ)).mul he'
  rwa [mul_one] at this

/-- **`r = 1` and `r = 1 + 2 * 3^m` agree mod `3^m`.** If `3 V(r) = 2[(c_0 + c_1) 2^r +
(2 c_0 - c_1)(-1)^r]` for these two values of `r`, then `V(1 + 2 * 3^m) ≡ V(1) (mod 3^m)`. -/
theorem thetaJ_value_cong (m : ℕ) (c0 c1 V1 Vr : ℤ)
    (h1 : 3 * V1 = 2 * ((c0 + c1) * 2 ^ 1 + (2 * c0 - c1) * (-1) ^ 1))
    (hr : 3 * Vr = 2 * ((c0 + c1) * 2 ^ (1 + 2 * 3 ^ m) + (2 * c0 - c1) * (-1) ^ (1 + 2 * 3 ^ m))) :
    Vr ≡ V1 [ZMOD 3 ^ m] := by
  have hodd : Odd (1 + 2 * 3 ^ m) := ⟨3 ^ m, by ring⟩
  rw [hodd.neg_one_pow] at hr
  have hd : (3 : ℤ) ^ (m + 1) ∣ 2 - 2 ^ (1 + 2 * 3 ^ m) := (two_pow_cong m).dvd
  have key : (3 : ℤ) ^ m * 3 ∣ (V1 - Vr) * 3 := by
    rw [← pow_succ]
    have : (V1 - Vr) * 3 = 2 * (c0 + c1) * (2 - 2 ^ (1 + 2 * 3 ^ m)) := by linarith
    rw [this]
    exact Dvd.dvd.mul_left hd _
  exact (Int.modEq_iff_dvd.2 (Int.dvd_of_mul_dvd_mul_right (by norm_num) key))

/-- A correction `h` vanishing on squarefree integers `> 1` acts on squarefree `n` as the scalar
`h(1)`: `(f * h)(n) = h(1) f(n)`. -/
theorem mul_corr_squarefree (f h : ArithmeticFunction ℤ)
    (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) {n : ℕ} (hn : Squarefree n) :
    (f * h) n = h 1 * f n := by
  rw [mul_apply, sum_eq_single_of_mem (n, 1) (by simp [hn.ne_zero])]
  · ring
  · intro x hx hne
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hb1 : x.2 ≠ 1 := by
      intro hb; apply hne
      rw [hb, mul_one] at hx
      exact Prod.ext hx.1 hb
    rw [hh x.2 (hn.squarefree_of_dvd (Dvd.intro_left _ hx.1)) hb1, mul_zero]

lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq d hdp hdq
    have hcop : Nat.gcd p q = 1 := (Nat.coprime_primes (hs p hp) (hs q hq)).2 hpq
    exact Nat.isUnit_iff.2 (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hdp hdq))
  · intro p hp; exact (Nat.prime_iff.1 (hs p hp)).squarefree

/-- **Theorem J (algebraic core).** Hypotheses (the theta-series facts, stated plainly):
`S` is an infinite set of primes (Chebotarev); `r_0, r_1, a_0, a_ψ` satisfy (T1) at every `n`;
on a product of the primes of any finite `s ⊆ S`, `a_0 = 2^|s|` and `a_ψ = (-1)^|s|`.
Then for all integers `c_0, c_1` and every correction `h` vanishing on squarefree `n > 1`, the
filter `F = (c_0 r_0 + c_1 r_1) * h` cannot be nonzero mod `3^m` at every selected prime while
vanishing mod `3^m` on every product of at least two distinct selected primes. -/
theorem thetaJ_no_filter (m : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (r0 r1 a0 apsi : ArithmeticFunction ℤ)
    (hT1 : ∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n)
    (hval : ∀ s : Finset ℕ, ↑s ⊆ S →
      a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = (-1) ^ s.card)
    (c0 c1 : ℤ) (theta : ArithmeticFunction ℤ) (htheta : ∀ n, theta n = c0 * r0 n + c1 * r1 n)
    (h : ArithmeticFunction ℤ) (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ (theta * h) q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ (theta * h) (∏ p ∈ s, p))) := by
  rintro ⟨hprime, hcomp⟩
  obtain ⟨s, hsS, hcard⟩ := hinf.exists_subset_card_eq (1 + 2 * 3 ^ m)
  have hs_pr : ∀ p ∈ s, p.Prime := fun p hp => hS p (hsS hp)
  obtain ⟨q, hq⟩ : s.Nonempty := by rw [← card_pos, hcard]; positivity
  have hqS : q ∈ S := hsS hq
  -- values of the theta combination
  have vS := thetaJ_value c0 c1 (r0 (∏ p ∈ s, p)) (r1 (∏ p ∈ s, p)) (a0 (∏ p ∈ s, p))
    (apsi (∏ p ∈ s, p)) s.card (hT1 _).1 (hT1 _).2 (hval s hsS).1 (hval s hsS).2
  have hq1 : ↑({q} : Finset ℕ) ⊆ S := by simpa using hqS
  have vq := thetaJ_value c0 c1 (r0 q) (r1 q) (a0 q) (apsi q) 1 (hT1 _).1 (hT1 _).2
    (by simpa using (hval {q} hq1).1) (by simpa using (hval {q} hq1).2)
  rw [hcard] at vS
  have hc := thetaJ_value_cong m c0 c1 _ _ vq vS
  -- the filter on the squarefree arguments
  have hFS := mul_corr_squarefree theta h hh (squarefree_prod_primes hs_pr)
  have hFq := mul_corr_squarefree theta h hh
    (Nat.prime_iff.1 (hS q hqS)).squarefree
  have hdS := hcomp s hsS (by rw [hcard]; have := Nat.one_le_pow m 3 (by norm_num); omega)
  apply hprime q hqS
  rw [hFq]
  rw [hFS] at hdS
  rw [htheta] at hdS ⊢
  have := (hc.mul_left (h 1)).dvd
  have e := dvd_add hdS this
  rwa [add_sub_cancel] at e

/-! ## Non-vacuity: the hypotheses of `thetaJ_no_filter` are satisfiable -/

/-- `n ↦ u^ω(n)` (value 0 at 0). -/
def powOmega (u : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else u ^ (n.primeFactors.card), by simp⟩

lemma powOmega_apply (u : ℤ) (n : ℕ) :
    powOmega u n = if n = 0 then 0 else u ^ (n.primeFactors.card) := rfl

lemma powOmega_prod (u : ℤ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    powOmega u (∏ p ∈ s, p) = u ^ s.card := by
  have hne : ∏ p ∈ s, p ≠ 0 := prod_ne_zero_iff.2 fun p hp => (hs p hp).ne_zero
  rw [powOmega_apply, if_neg hne, Nat.primeFactors_prod hs]

/-- A model of the hypotheses: `S` = all primes, `a_0 = 2^ω`, `a_ψ = (-1)^ω`,
`r_1 = (2 a_0 - 2 a_ψ)/3`, `r_0 = 2 a_ψ + r_1`. -/
theorem thetaJ_hyps_consistent :
    ∃ (S : Set ℕ) (r0 r1 a0 apsi : ArithmeticFunction ℤ),
      (∀ q ∈ S, q.Prime) ∧ S.Infinite ∧
      (∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S →
        a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = (-1) ^ s.card) := by
  let a0 := powOmega 2
  let apsi := powOmega (-1)
  let r1 : ArithmeticFunction ℤ := ⟨fun n => (2 * a0 n - 2 * apsi n) / 3, by simp⟩
  let r0 : ArithmeticFunction ℤ := ⟨fun n => 2 * apsi n + r1 n, by simp⟩
  refine ⟨{p | p.Prime}, r0, r1, a0, apsi, fun q hq => hq, Nat.infinite_setOfPred_prime, ?_, ?_⟩
  · intro n
    have hr1 : r1 n = (2 * a0 n - 2 * apsi n) / 3 := rfl
    have hr0 : r0 n = 2 * apsi n + r1 n := rfl
    have h3 : (3 : ℤ) ∣ 2 * a0 n - 2 * apsi n := by
      simp only [a0, apsi, powOmega_apply]
      split_ifs
      · simp
      · have : (2 : ℤ) ^ n.primeFactors.card ≡ (-1) ^ n.primeFactors.card [ZMOD 3] :=
          Int.ModEq.pow _ (by decide)
        have := (this.mul_left 2).dvd
        rw [← dvd_neg, neg_sub]; exact this
    have e : 3 * r1 n = 2 * a0 n - 2 * apsi n := by rw [hr1]; exact Int.mul_ediv_cancel' h3
    exact ⟨by linarith, by linarith⟩
  · intro s hs
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs hp
    exact ⟨powOmega_prod 2 hs', powOmega_prod (-1) hs'⟩

end M2L3
