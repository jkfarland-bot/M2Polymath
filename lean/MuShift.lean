/-
Run r25 / M2, seat M2L2 (item 6): the R-053 index shift through Theorem H's moment argument
(cold read m2/cr/REPORT_cold_read.md, point 7, the `Q(t)` form).

A `mu` identity at levels `0..L` on squarefree `n`,
`mu(n) = sum over z <= L of (zeta ^ z * g_z)(n) (mod p^k)` with `g_z` vanishing on squarefree
`m > 1` (for example `g_z = E_p(h_z)`), gives on the slice integers `c_z = g_z(1)` with
`sum_z c_z z^r = (-1)^r (mod p^k)` for every `r`; the node polynomial
`Q(t) = prod over z <= L of (t - z)` then gives `0 = sum_z c_z Q(z) = Q(-1) = (-1)^(L+1) (L+1)!
(mod p^k)`, so `k <= v_p((L+1)!)` and `L + 1 >= S(p^k)`. (This is the cold read's shifted-node
argument `w = z + 1`, `q_0 = prod (-w)`, written without the shift.)

Contents.
1. `mu_moment_dvd`, `mu_moment_kempner`: moment level (only `0 <= r <= L + 1` is used).
2. `mu_slice_kempner`: the arithmetic-function form (corrections vanishing on squarefree `m > 1`).
3. Connection to the r25 library: `Ep_squarefree` (`E_p(g)` vanishes on squarefree `m > 1`),
   `hasLevel_zeta_kempner`: every `HasLevel p (Ep p) zetaZ k L` identity (r25's level form of
   `mu = sum_(z <= L) zeta^z E_p(g_z) (mod p^k)`) has `S(p^k) <= L + 1`;
   `levelCount_zetaZ_via_H`: `L_zeta(p, k) + 1 = S(p^k)` with the lower bound from this file and
   the upper bound from r25 (`levelCount_add_one_le_kempner`); it agrees with r25's
   `levelCount_zetaZ_int`, proved there by a different route.

Lean v4.33.1 with Mathlib; imports the r25 library, round 1, FamGen and A1.
-/
import Mathlib
import Found
import DirBase
import DirMain
import Moment
import MomentZ
import Slice
import Construct
import FamGen
import A1

namespace M2L2

open Finset ArithmeticFunction M2L Polynomial
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius Nat

/-! ## 1. Moment level -/

/-- `sum_z a_z P(z) = sum_i P_i s_i` for a polynomial of degree below `n`. -/
theorem sum_mul_eval0 (T : Finset ℤ) (a : ℤ → ℤ) (P : ℤ[X]) {n : ℕ} (hP : P.natDegree < n) :
    ∑ z ∈ T, a z * P.eval z = ∑ i ∈ range n, P.coeff i * mom T a i := by
  simp_rw [eval_eq_sum_range' hP, mom, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro z _
  ring

/-- Levels `0..L` as integer nodes. -/
noncomputable def levelNodes (L : ℕ) : Finset ℤ := (range (L + 1)).image (fun z : ℕ => (z : ℤ))

theorem levelNodes_card (L : ℕ) : (levelNodes L).card = L + 1 := by
  rw [levelNodes, card_image_of_injective _ Nat.cast_injective, card_range]

theorem mom_levelNodes (L : ℕ) (c : ℕ → ℤ) (r : ℕ) :
    mom (levelNodes L) (fun z => c z.toNat) r = ∑ z ∈ range (L + 1), c z * (z : ℤ) ^ r := by
  rw [mom, levelNodes, sum_image (fun x _ y _ h => Nat.cast_injective h)]
  simp

theorem nodePoly_levelNodes_eval_neg_one (L : ℕ) :
    (nodePoly (levelNodes L)).eval (-1) = (-1) ^ (L + 1) * ((L + 1)! : ℤ) := by
  rw [nodePoly, eval_prod, levelNodes, prod_image (fun x _ y _ h => Nat.cast_injective h)]
  simp only [eval_sub, eval_X, eval_C]
  have : ∀ z ∈ range (L + 1), (-1 - (z : ℤ)) = (-1) * ((z : ℤ) + 1) := fun z _ => by ring
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_range]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast; rfl

/-- **Moment level.** If `sum_(z <= L) c_z z^r = (-1)^r (mod p^k)` for `0 <= r <= L + 1`, then
`p^k | (L+1)!`. -/
theorem mu_moment_dvd (p : ℕ) {k L : ℕ} (c : ℕ → ℤ)
    (hc : ∀ r, r ≤ L + 1 → (p : ℤ) ^ k ∣ ∑ z ∈ range (L + 1), c z * (z : ℤ) ^ r - (-1) ^ r) :
    (p : ℤ) ^ k ∣ ((L + 1)! : ℤ) := by
  set T := levelNodes L
  set a : ℤ → ℤ := fun z => c z.toNat
  set Q := nodePoly T
  have hQd : Q.natDegree < L + 2 := by rw [nodePoly_natDegree, levelNodes_card]; omega
  have h0 : ∑ z ∈ T, a z * Q.eval z = 0 :=
    sum_eq_zero fun z hz => by rw [nodePoly_eval_node hz, mul_zero]
  rw [sum_mul_eval0 T a Q hQd] at h0
  have hdiff : (p : ℤ) ^ k ∣ ∑ i ∈ range (L + 2), Q.coeff i * (mom T a i - (-1) ^ i) :=
    dvd_sum fun i hi => by
      rw [mom_levelNodes]
      exact (hc i (by have := mem_range.mp hi; omega)).mul_left _
  have hev : Q.eval (-1) = ∑ i ∈ range (L + 2), Q.coeff i * (-1) ^ i := eval_eq_sum_range' hQd _
  have key : ∑ i ∈ range (L + 2), Q.coeff i * (mom T a i - (-1) ^ i) = -Q.eval (-1) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, h0, hev, zero_sub]
  rw [key, dvd_neg, nodePoly_levelNodes_eval_neg_one] at hdiff
  have hu : IsUnit ((-1 : ℤ) ^ (L + 1)) := (isUnit_neg_one (α := ℤ)).pow _
  exact (hu.dvd_mul_left).1 hdiff

/-- **Moment level, Kempner form.** Under the hypothesis of `mu_moment_dvd`:
`k <= v_p((L+1)!)` and `S(p^k) <= L + 1`. -/
theorem mu_moment_kempner (p : ℕ) [hp : Fact p.Prime] {k L : ℕ} (c : ℕ → ℤ)
    (hc : ∀ r, r ≤ L + 1 → (p : ℤ) ^ k ∣ ∑ z ∈ range (L + 1), c z * (z : ℤ) ^ r - (-1) ^ r) :
    k ≤ padicValNat p (L + 1)! ∧ FrobLevel.kempner p k ≤ L + 1 := by
  have h := mu_moment_dvd p c hc
  have h' : p ^ k ∣ (L + 1)! := by exact_mod_cast h
  have hv := (FrobLevel.pow_dvd_factorial_iff p k (L + 1)).1 h'
  exact ⟨hv, FrobLevel.kempner_le p hv⟩

/-! ## 2. Arithmetic-function form -/

theorem zeta_pow_prime (z : ℕ) {q : ℕ} (hq : q.Prime) :
    ((ζ : ArithmeticFunction ℤ) ^ z) q = z := by
  rw [pow_apply_prime' zeta_int_one _ hq, zeta_int_prime hq, mul_one]

theorem moebius_squarefree' {n : ℕ} (hn : Squarefree n) :
    (μ : ArithmeticFunction ℤ) n = (-1) ^ ω n := by
  rw [moebius_apply_of_squarefree hn, cardDistinctFactors_eq_cardFactors_iff_squarefree
    hn.ne_zero |>.2 hn]

/-- **Arithmetic form.** If `mu(n) = sum over z <= L of (zeta ^ z * g_z)(n) (mod p^k)` on every
squarefree `n`, with `g_z` vanishing on squarefree `m > 1`, then `k <= v_p((L+1)!)` and
`S(p^k) <= L + 1`. -/
theorem mu_slice_kempner (p : ℕ) [hp : Fact p.Prime] {k L : ℕ} (g : ℕ → ArithmeticFunction ℤ)
    (hg : ∀ z, z ≤ L → ∀ m, Squarefree m → 1 < m → g z m = 0)
    (hmu : ∀ n, Squarefree n → (p : ℤ) ^ k ∣
      (μ : ArithmeticFunction ℤ) n - ∑ z ∈ range (L + 1), ((ζ : ArithmeticFunction ℤ) ^ z * g z) n) :
    k ≤ padicValNat p (L + 1)! ∧ FrobLevel.kempner p k ≤ L + 1 := by
  apply mu_moment_kempner p (fun z => g z 1)
  intro r _
  obtain ⟨n, hn, hnr, -⟩ := exists_slice {q | q.Prime} Nat.infinite_setOfPred_prime
    (fun _ hq => hq) r
  have h := hmu n hn
  have e : ∑ z ∈ range (L + 1), ((ζ : ArithmeticFunction ℤ) ^ z * g z) n =
      ∑ z ∈ range (L + 1), g z 1 * (z : ℤ) ^ r := by
    apply sum_congr rfl
    intro z hz
    have hz' : z ≤ L := by have := mem_range.mp hz; omega
    rw [mul_apply_squarefree _ _ hn (hg z hz'),
      apply_squarefree_of_mult (isMultiplicative_zeta.natCast.pow) hn
        (fun q hq _ => zeta_pow_prime z hq), hnr]
    ring
  rw [e, moebius_squarefree' hn, hnr] at h
  rw [← neg_sub]; exact h.neg_right

/-! ## 3. Connection to the r25 level statement -/

open FrobLevel FrobLevel.Dir in
/-- `E_p(g)` vanishes on squarefree `m > 1`. -/
theorem Ep_squarefree (p : ℕ) [hp : Fact p.Prime] (g : ArithmeticFunction ℤ) {m : ℕ}
    (hm : Squarefree m) (hm1 : 1 < m) : Ep p g m = 0 := by
  rw [Ep_apply]
  apply frobPush_apply_of_not
  rintro ⟨j, hj⟩
  have hj0 : j ≠ 0 := by rintro rfl; rw [zero_pow hp.out.ne_zero] at hj; omega
  have hj1 : j ≠ 1 := by rintro rfl; rw [one_pow] at hj; omega
  have hdvd : j * j ∣ m := by
    rw [← hj, ← pow_two]; exact pow_dvd_pow j hp.out.two_le
  have := hm j hdvd
  exact hj1 (Nat.isUnit_iff.mp this)

open FrobLevel FrobLevel.Dir in
/-- **R-053 lower bound via Theorem H's moment argument.** Every r25 level identity
`HasLevel p (Ep p) zetaZ k L` (that is, `1 = zeta * sum_(z <= L) zeta^z E_p(g_z) (mod p^k)` in
the Dirichlet ring, equivalently `mu = sum_(z <= L) zeta^z E_p(g_z) (mod p^k)`) has
`S(p^k) <= L + 1` (and `k <= v_p((L+1)!)`). -/
theorem hasLevel_zeta_kempner (p : ℕ) [hp : Fact p.Prime] {k L : ℕ}
    (h : HasLevel p (Ep p) zetaZ k L) :
    k ≤ padicValNat p (L + 1)! ∧ kempner p k ≤ L + 1 := by
  obtain ⟨g, Y, hY⟩ := h
  set S := ∑ z ∈ range (L + 1), zetaZ ^ z * Ep p (g z)
  have hmuS : (μ : ArithmeticFunction ℤ) - S =
      ((p ^ k : ℕ) : ArithmeticFunction ℤ) * ((μ : ArithmeticFunction ℤ) * Y) := by
    have e1 : (μ : ArithmeticFunction ℤ) * zetaZ = 1 := moebius_mul_coe_zeta
    have := congrArg (fun F => (μ : ArithmeticFunction ℤ) * F) hY
    rw [mul_sub, mul_one, ← mul_assoc, e1, one_mul] at this
    rw [this]; push_cast; ring
  apply mu_slice_kempner p (fun z => Ep p (g z))
    (fun z _ m hm hm1 => Ep_squarefree p (g z) hm hm1)
  intro n _
  have := congrArg (fun F : ArithmeticFunction ℤ => F n) hmuS
  rw [sub_apply', natCast_mul_apply, FrobLevel.Dir.sum_apply'] at this
  rw [this]
  push_cast
  exact dvd_mul_right _ _

open FrobLevel FrobLevel.Dir in
/-- **`L_zeta(p, k) + 1 = S(p^k)`** with the lower bound from `hasLevel_zeta_kempner` and the
upper bound (existence at level `S(p^k) - 1`) from r25. Same statement as r25's
`levelCount_zetaZ_int`, whose lower bound is proved there by restriction to smooth numbers. -/
theorem levelCount_zetaZ_via_H (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) zetaZ k + 1 = kempner p k := by
  have hR : ∀ a : ℤ, (p : ℤ) ∣ a ^ p - a := fermat_int p
  have hU : IsUnit zetaZ := by
    rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, zetaZ_apply one_ne_zero]; exact isUnit_one
  have hup := levelCount_add_one_le_kempner p hR zetaZ hU hk
  have hlow := (hasLevel_zeta_kempner p (hasLevel_levelCount (hasLevel_kempner p hR zetaZ hU hk))).2
  omega

end M2L2
