/-
Run r25 / M2, seat M2L: the moment core of Theorems B and H (A19, Q2 and Q5), over the integers.

For a finite set `T` of integer nodes and integer weights `a`, the moments are
`mom T a r = sum over z in T of a z * z ^ r`.

Contents.
1. `thmB_moment` (Theorem B, exact form): if `s_1 = p u (mod p^2)` and `s_r = 0 (mod p^2)` for
   one `r >= 2` with `p (p - 1) | r - 1`, then `sum over v_p(z) = 1 of a_z (z / p) = u (mod p)`;
   `thmB_moment_exists`: if moreover `p` does not divide `u`, some node `z` with `v_p(z) = 1`
   has `a_z` not divisible by `p`.
2. `thmH_moment` (Theorem H, lower bound): if `0` is not a node, `s_1 = p^v u (mod p^(v+k))`
   with `p` not dividing `u`, and `s_r = 0 (mod p^(v+k))` for `2 <= r <= |T| + 1`, then
   `k <= sum over z in T of v_p(z)`.
3. Kempner consequences: the node sum of `v_p` is at most `v_p(Z!)` on `{1..Z}` and at most
   `2 v_p(Z!)` on `{-Z..Z} \ {0}`; hence `S(p^k) <= Z` (cheap) and `S(p^ceil(k/2)) <= Z`
   (signed), with `S = kempner` from Found.lean.
4. Construction at the moment level (adjugate of the moment matrix, then division by the node
   polynomial): for every nonempty node set without `0` there are weights with `s_1 = C != 0`
   and `C * prod z | s_r` for every `r >= 2`.
5. Exact minimal node bounds for the moment target: `cheap_moment_iff`, `signed_moment_iff`.

Lean v4.33.1 with Mathlib; imports Found (r25 library). No sorry.
-/
import Mathlib
import Found

namespace M2L

open Finset Polynomial

/-! ## 0. Moments and the node polynomial -/

/-- The `r`-th moment `s_r = sum over z in T of a z * z ^ r`. -/
def mom (T : Finset ℤ) (a : ℤ → ℤ) (r : ℕ) : ℤ := ∑ z ∈ T, a z * z ^ r

/-- The node polynomial `Q(t) = prod over z in T of (t - z)`. -/
noncomputable def nodePoly (T : Finset ℤ) : ℤ[X] := ∏ z ∈ T, (X - C z)

theorem nodePoly_monic (T : Finset ℤ) : (nodePoly T).Monic :=
  monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z

theorem nodePoly_natDegree (T : Finset ℤ) : (nodePoly T).natDegree = T.card := by
  rw [nodePoly, natDegree_finsetProd_X_sub_C_eq_card]

theorem nodePoly_eval_node {T : Finset ℤ} {z : ℤ} (hz : z ∈ T) : (nodePoly T).eval z = 0 := by
  rw [nodePoly, eval_prod]
  exact prod_eq_zero hz (by simp)

theorem nodePoly_coeff_zero (T : Finset ℤ) : (nodePoly T).coeff 0 = ∏ z ∈ T, -z := by
  rw [coeff_zero_eq_eval_zero, nodePoly, eval_prod]
  simp

/-- `sum a_z z P(z) = sum_i P_i s_(i+1)` for any polynomial of degree below `n`. -/
theorem sum_mul_eval (T : Finset ℤ) (a : ℤ → ℤ) (P : ℤ[X]) {n : ℕ} (hP : P.natDegree < n) :
    ∑ z ∈ T, a z * z * P.eval z = ∑ i ∈ range n, P.coeff i * mom T a (i + 1) := by
  simp_rw [eval_eq_sum_range' hP, mom, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro z _
  ring

/-- The moment recurrence at the first moment: `sum_(i <= d) q_i s_(i+1) = 0`. -/
theorem nodePoly_moment_rel (T : Finset ℤ) (a : ℤ → ℤ) :
    ∑ i ∈ range (T.card + 1), (nodePoly T).coeff i * mom T a (i + 1) = 0 := by
  rw [← sum_mul_eval T a (nodePoly T) (by rw [nodePoly_natDegree]; omega)]
  exact sum_eq_zero fun z hz => by rw [nodePoly_eval_node hz, mul_zero]

/-! ## 1. Valuations of products -/

section Val

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
theorem padicValInt_neg' (z : ℤ) : padicValInt p (-z) = padicValInt p z := by
  simp [padicValInt]

theorem padicValInt_prod (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) :
    padicValInt p (∏ z ∈ T, z) = ∑ z ∈ T, padicValInt p z := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ mem_insert_self x s)
    have hs0 : (0 : ℤ) ∉ s := fun h => h0 (mem_insert_of_mem h)
    rw [prod_insert hx, sum_insert hx, padicValInt.mul hx0 (prod_ne_zero_iff.mpr fun z hz h =>
      hs0 (h ▸ hz)), ih hs0]

theorem pow_dvd_prod_iff (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (k : ℕ) :
    (p : ℤ) ^ k ∣ ∏ z ∈ T, z ↔ k ≤ ∑ z ∈ T, padicValInt p z := by
  rw [padicValInt_dvd_iff, padicValInt_prod p T h0]
  have : ∏ z ∈ T, z ≠ 0 := prod_ne_zero_iff.mpr fun z hz h => h0 (h ▸ hz)
  simp [this]

theorem dvd_prod_neg_iff (T : Finset ℤ) (x : ℤ) : x ∣ ∏ z ∈ T, -z ↔ x ∣ ∏ z ∈ T, z := by
  rw [prod_neg]
  constructor
  · intro h
    have := h.mul_left ((-1) ^ T.card)
    rwa [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at this
  · intro h; exact h.mul_left _

theorem int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out

theorem isCoprime_pow_of_not_dvd {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (k : ℕ) :
    IsCoprime ((p : ℤ) ^ k) u :=
  ((Irreducible.coprime_iff_not_dvd (int_prime p).irreducible).2 hu).pow_left

end Val

/-! ## 2. Theorem H, lower bound -/

section H

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Theorem H (moment form, lower bound).** Nodes `T` not containing `0`, weights `a`, and
`p` prime. If `s_1 = p^v u (mod p^(v+k))` with `p` not dividing `u`, and
`s_r = 0 (mod p^(v+k))` for every `2 <= r <= |T| + 1`, then `k <= sum over z in T of v_p(z)`. -/
theorem thmH_moment (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (a : ℤ → ℤ) (v k : ℕ) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (h1 : (p : ℤ) ^ (v + k) ∣ mom T a 1 - p ^ v * u)
    (hr : ∀ r, 2 ≤ r → r ≤ T.card + 1 → (p : ℤ) ^ (v + k) ∣ mom T a r) :
    k ≤ ∑ z ∈ T, padicValInt p z := by
  have rel := nodePoly_moment_rel T a
  rw [sum_range_succ'] at rel
  set q0 := (nodePoly T).coeff 0
  have hrest : (p : ℤ) ^ (v + k) ∣
      ∑ i ∈ range T.card, (nodePoly T).coeff (i + 1) * mom T a (i + 1 + 1) :=
    dvd_sum fun i hi => (hr _ (by omega) (by have := mem_range.mp hi; omega)).mul_left _
  have hq : (p : ℤ) ^ (v + k) ∣ q0 * mom T a 1 := by
    have : q0 * mom T a 1 = -(∑ i ∈ range T.card,
        (nodePoly T).coeff (i + 1) * mom T a (i + 1 + 1)) := by linear_combination rel
    rw [this]; exact hrest.neg_right
  have hq2 : (p : ℤ) ^ v * (p : ℤ) ^ k ∣ (p : ℤ) ^ v * (q0 * u) := by
    rw [← pow_add]
    have := dvd_sub hq (h1.mul_left q0)
    have e : q0 * mom T a 1 - q0 * (mom T a 1 - p ^ v * u) = (p : ℤ) ^ v * (q0 * u) := by ring
    rwa [e] at this
  have hpv : (p : ℤ) ^ v ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hq3 : (p : ℤ) ^ k ∣ q0 := (isCoprime_pow_of_not_dvd p hu k).dvd_of_dvd_mul_right
    ((mul_dvd_mul_iff_left hpv).1 hq2)
  have hq0 : q0 = ∏ z ∈ T, -z := nodePoly_coeff_zero T
  rw [hq0, dvd_prod_neg_iff, pow_dvd_prod_iff p T h0] at hq3
  exact hq3

end H

/-! ## 3. Theorem B -/

section B

variable (p : ℕ) [hp : Fact p.Prime]

/-- Euler modulo `p^2`: if `p` does not divide `z` and `p (p - 1) | r - 1`, `r >= 1`, then
`p^2 | z^r - z`. -/
theorem euler_sq {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) {r : ℕ} (hr1 : 1 ≤ r) (hr : p * (p - 1) ∣ r - 1) :
    (p : ℤ) ^ 2 ∣ z ^ r - z := by
  obtain ⟨m, hm⟩ := hr
  have hcop : IsCoprime z (p : ℤ) :=
    ((Irreducible.coprime_iff_not_dvd (int_prime p).irreducible).2 hz).symm
  have hf : (p : ℤ) ∣ z ^ (p - 1) - 1 :=
    (Int.ModEq.pow_card_sub_one_eq_one hp.out hcop).symm.dvd
  have h2 : (p : ℤ) ^ (1 + 1) ∣ (z ^ (p - 1)) ^ p ^ 1 - 1 ^ p ^ 1 := dvd_sub_pow_of_dvd_sub hf 1
  rw [one_pow, pow_one, ← pow_mul] at h2
  have h3 : (p : ℤ) ^ 2 ∣ (z ^ ((p - 1) * p)) ^ m - 1 := h2.trans (sub_one_dvd_pow_sub_one _ m)
  have e : z ^ r - z = z * ((z ^ ((p - 1) * p)) ^ m - 1) := by
    rw [← pow_mul, mul_sub, mul_one, ← pow_succ']
    congr 2
    rw [mul_comm (p - 1) p, ← hm]; omega
  rw [e]; exact h3.mul_left z

/-- The per-node congruence behind Theorem B: for `r >= 2` with `p (p - 1) | r - 1`,
`z - z^r = [v_p(z) = 1] z (mod p^2)`. -/
theorem node_congr (z : ℤ) {r : ℕ} (hr2 : 2 ≤ r) (hr : p * (p - 1) ∣ r - 1) :
    (p : ℤ) ^ 2 ∣ (z - z ^ r) - (if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0) := by
  have hzr : (p : ℤ) ∣ z → (p : ℤ) ^ 2 ∣ z ^ r := fun h =>
    (pow_dvd_pow_of_dvd h 2).trans (pow_dvd_pow z hr2)
  by_cases h1 : (p : ℤ) ∣ z
  · by_cases h2 : (p : ℤ) ^ 2 ∣ z
    · rw [if_neg (fun h => h.2 h2), sub_zero]; exact dvd_sub h2 (hzr h1)
    · rw [if_pos ⟨h1, h2⟩]
      have : z - z ^ r - z = -(z ^ r) := by ring
      rw [this]; exact (hzr h1).neg_right
  · rw [if_neg (fun h => h1 h.1), sub_zero]
    have := euler_sq p h1 (by omega) hr
    rw [← neg_sub]; exact this.neg_right

/-- The nodes with exactly one factor of `p`. -/
def val1 (p : ℕ) (T : Finset ℤ) : Finset ℤ :=
  T.filter fun z => (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z

/-- **Theorem B (moment form, exact).** If `s_1 = p u (mod p^2)` and `s_r = 0 (mod p^2)` for one
`r >= 2` with `p (p - 1) | r - 1` (for example `r = 1 + p (p - 1)`), then
`sum over nodes z with v_p(z) = 1 of a_z (z / p) = u (mod p)`. -/
theorem thmB_moment (T : Finset ℤ) (a : ℤ → ℤ) (u : ℤ) {r : ℕ} (hr2 : 2 ≤ r)
    (hr : p * (p - 1) ∣ r - 1) (h1 : (p : ℤ) ^ 2 ∣ mom T a 1 - p * u)
    (hs : (p : ℤ) ^ 2 ∣ mom T a r) :
    (p : ℤ) ∣ ∑ z ∈ val1 p T, a z * (z / p) - u := by
  have hsum : (p : ℤ) ^ 2 ∣ (mom T a 1 - mom T a r) -
      ∑ z ∈ T, a z * (if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0) := by
    have e : (mom T a 1 - mom T a r) -
        ∑ z ∈ T, a z * (if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0) =
        ∑ z ∈ T, a z * ((z - z ^ r) - (if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0)) := by
      simp only [mom, pow_one, ← sum_sub_distrib]
      apply sum_congr rfl; intro z _; ring
    rw [e]
    exact dvd_sum fun z _ => (node_congr p z hr2 hr).mul_left _
  have hfilt : ∑ z ∈ T, a z * (if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0) =
      (p : ℤ) * ∑ z ∈ val1 p T, a z * (z / p) := by
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter, Finset.mul_sum, val1]
    apply sum_congr rfl
    intro z hz
    have hpz := ((mem_filter.mp hz).2).1
    rw [← mul_assoc, mul_comm (p : ℤ), mul_assoc, Int.mul_ediv_cancel' hpz]
  rw [hfilt] at hsum
  have key : (p : ℤ) ^ 2 ∣ (p : ℤ) * (∑ z ∈ val1 p T, a z * (z / p) - u) := by
    have := dvd_sub (dvd_sub h1 hs) hsum
    have e : mom T a 1 - p * u - mom T a r - (mom T a 1 - mom T a r -
        (p : ℤ) * ∑ z ∈ val1 p T, a z * (z / p)) =
        (p : ℤ) * (∑ z ∈ val1 p T, a z * (z / p) - u) := by ring
    rwa [e] at this
  rw [pow_two] at key
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.out.ne_zero)).1 key

/-- **Theorem B (moment form, existence).** Under the hypotheses of `thmB_moment` with `p` not
dividing `u`, some node `z` with `v_p(z) = 1` has weight `a_z` not divisible by `p`. -/
theorem thmB_moment_exists (T : Finset ℤ) (a : ℤ → ℤ) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) {r : ℕ}
    (hr2 : 2 ≤ r) (hr : p * (p - 1) ∣ r - 1) (h1 : (p : ℤ) ^ 2 ∣ mom T a 1 - p * u)
    (hs : (p : ℤ) ^ 2 ∣ mom T a r) :
    ∃ z ∈ T, (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧ ¬ (p : ℤ) ∣ a z := by
  by_contra hne
  push Not at hne
  have hall : (p : ℤ) ∣ ∑ z ∈ val1 p T, a z * (z / p) := dvd_sum fun z hz => by
    have hz' := mem_filter.mp hz
    exact (hne z hz'.1 hz'.2.1 hz'.2.2).mul_right _
  have := thmB_moment p T a u hr2 hr h1 hs
  exact hu (by have := dvd_sub hall this; rwa [sub_sub_cancel] at this)

/-- The admissible exponent `r = 1 + p (p - 1)`. -/
theorem thmB_moment_std (T : Finset ℤ) (a : ℤ → ℤ) (u : ℤ)
    (h1 : (p : ℤ) ^ 2 ∣ mom T a 1 - p * u) (hs : (p : ℤ) ^ 2 ∣ mom T a (1 + p * (p - 1))) :
    (p : ℤ) ∣ ∑ z ∈ val1 p T, a z * (z / p) - u := by
  have h2 := hp.out.two_le
  refine thmB_moment p T a u ?_ (by simp) h1 hs
  have : 1 ≤ p * (p - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

end B

end M2L
