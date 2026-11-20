/-
Run r25 / M2, seat M2L: Kempner consequences of Theorem H and the matching construction, at the
moment level (integer nodes, integer weights).

Contents.
1. `sum_val_cheap`, `sum_val_signed`: the node sum of `v_p` over `{1..Z}` is `v_p(Z!)`, over
   `{-Z..-1} union {1..Z}` it is `2 v_p(Z!)`.
2. `exists_weights`: for a nonempty node set without `0`, weights with `s_1 != 0` and
   `s_r = 0` for `2 <= r <= |T|` (the adjugate of the moment matrix, which is a transposed
   Vandermonde matrix times a diagonal).
3. `construct_moment`: those weights have `s_1 * prod z | s_r` for every `r >= 2`
   (division of `X^(r-1)` by the node polynomial).
4. `MomentTarget p k T a`: some `v`, `u` with `p` not dividing `u`,
   `s_1 = p^v u (mod p^(v+k))` and `s_r = 0 (mod p^(v+k))` for all `r >= 2`.
   `cheap_moment_iff`: achievable on nodes in `{1..Z}` iff `S(p^k) <= Z`;
   `signed_moment_iff`: achievable on nodes in `{-Z..-1} union {1..Z}` iff
   `S(p^ceil(k/2)) <= Z` (`ceil(k/2)` written `(k + 1) / 2`). `S = FrobLevel.kempner`.

Lean v4.33.1 with Mathlib; imports Found (r25 library) and Moment. No sorry.
-/
import Mathlib
import Found
import Moment

namespace M2L

open Finset Polynomial
open scoped Nat

/-- Cheap (unsigned) node set `{1, ..., Z}`. -/
noncomputable def cheapNodes (Z : ℕ) : Finset ℤ := Icc 1 (Z : ℤ)

/-- Signed node set `{-Z, ..., -1} union {1, ..., Z}`. -/
noncomputable def signedNodes (Z : ℕ) : Finset ℤ := Icc (-(Z : ℤ)) (-1) ∪ Icc 1 (Z : ℤ)

theorem zero_not_mem_cheap (Z : ℕ) : (0 : ℤ) ∉ cheapNodes Z := by simp [cheapNodes]

theorem zero_not_mem_signed (Z : ℕ) : (0 : ℤ) ∉ signedNodes Z := by simp [signedNodes]

theorem cheap_subset_signed (Z : ℕ) : cheapNodes Z ⊆ signedNodes Z :=
  subset_union_right

section Kempner

variable (p : ℕ) [hp : Fact p.Prime]

theorem sum_val_cheap (Z : ℕ) : ∑ z ∈ cheapNodes Z, padicValInt p z = padicValNat p Z ! := by
  induction Z with
  | zero => simp [cheapNodes]
  | succ Z ih =>
    have e : cheapNodes (Z + 1) = insert ((Z : ℤ) + 1) (cheapNodes Z) := by
      ext x; simp [cheapNodes]; omega
    have hn : ((Z : ℤ) + 1) ∉ cheapNodes Z := by simp [cheapNodes]
    rw [e, sum_insert hn, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero Z) (Nat.factorial_ne_zero Z)]
    have : ((Z : ℤ) + 1) = ((Z + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, padicValInt.of_nat]

theorem sum_val_signed (Z : ℕ) :
    ∑ z ∈ signedNodes Z, padicValInt p z = 2 * padicValNat p Z ! := by
  have hdisj : Disjoint (Icc (-(Z : ℤ)) (-1)) (Icc 1 (Z : ℤ)) := by
    rw [disjoint_left]; intro x hx hx'; simp at hx hx'; omega
  have himg : Icc (-(Z : ℤ)) (-1) = (cheapNodes Z).image (fun z => -z) := by
    ext x; simp only [cheapNodes, mem_Icc, mem_image]
    constructor
    · intro h; exact ⟨-x, by omega, by ring⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [signedNodes, sum_union hdisj, himg, sum_image (fun x _ y _ h => neg_injective h)]
  simp_rw [padicValInt_neg']
  rw [← cheapNodes, sum_val_cheap]
  ring

theorem kempner_dvd_factorial {k Z : ℕ} (h : FrobLevel.kempner p k ≤ Z) : k ≤ padicValNat p Z ! :=
  (FrobLevel.pow_dvd_factorial_iff p k Z).1
    (((FrobLevel.pow_dvd_factorial_iff p k _).2 (FrobLevel.kempner_spec p k)).trans
      (Nat.factorial_dvd_factorial h))

end Kempner

/-! ## Construction of weights -/

section Construct

/-- **Weights by the adjugate.** For a nonempty node set `T` without `0` there are integer
weights with `s_1 != 0` and `s_r = 0` for `2 <= r <= |T|`. -/
theorem exists_weights (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (hne : T.Nonempty) :
    ∃ a : ℤ → ℤ, mom T a 1 ≠ 0 ∧ ∀ r, 2 ≤ r → r ≤ T.card → mom T a r = 0 := by
  classical
  set d := T.card with hd
  have hd0 : 0 < d := card_pos.mpr hne
  let e : Fin d ≃ T := T.equivFin.symm
  let w : Fin d → ℤ := fun i => (e i : ℤ)
  let M : Matrix (Fin d) (Fin d) ℤ := fun i j => w j ^ ((i : ℕ) + 1)
  let i0 : Fin d := ⟨0, hd0⟩
  let b : Fin d → ℤ := fun j => M.adjugate j i0
  let a : ℤ → ℤ := fun z => if h : z ∈ T then b (e.symm ⟨z, h⟩) else 0
  have hM : M = (Matrix.vandermonde w).transpose * Matrix.diagonal w := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply]
    show w j ^ ((i : ℕ) + 1) = _
    rw [pow_succ]
  have hw0 : ∀ j, w j ≠ 0 := fun j h => h0 (h ▸ (e j).2)
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    refine mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
      (prod_ne_zero_iff.mpr fun j _ => hw0 j)
    intro i j h
    exact e.injective (Subtype.ext h)
  have hmom : ∀ r, mom T a r = ∑ j, b j * w j ^ r := by
    intro r
    rw [mom, ← sum_coe_sort T (fun z => a z * z ^ r), ← e.sum_comp]
    apply sum_congr rfl
    intro j _
    simp only [a, w, dif_pos (e j).2, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hrow : ∀ i : Fin d, mom T a ((i : ℕ) + 1) = if i = i0 then M.det else 0 := by
    intro i
    rw [hmom]
    have := congrFun (congrFun (Matrix.mul_adjugate M) i) i0
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at this
    rw [← this]
    apply sum_congr rfl
    intro j _
    simp only [b, M]
    ring
  refine ⟨a, ?_, ?_⟩
  · have := hrow i0
    rw [if_pos rfl] at this
    rw [show (1 : ℕ) = ((i0 : ℕ) + 1) from rfl, this]
    exact hdet
  · intro r hr2 hrd
    have := hrow ⟨r - 1, by omega⟩
    rw [if_neg (fun h => by
      have := congrArg Fin.val h; simp [i0] at this; omega)] at this
    rwa [show ((⟨r - 1, by omega⟩ : Fin d) : ℕ) + 1 = r by simp; omega] at this

/-- **Construction (moment level).** For a nonempty node set `T` without `0` there are integer
weights with `s_1 = C != 0` and `C * prod over z in T of z | s_r` for every `r >= 2`. -/
theorem construct_moment (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (hne : T.Nonempty) :
    ∃ a : ℤ → ℤ, mom T a 1 ≠ 0 ∧ ∀ r, 2 ≤ r → mom T a 1 * ∏ z ∈ T, z ∣ mom T a r := by
  obtain ⟨a, hC, hz⟩ := exists_weights T h0 hne
  refine ⟨a, hC, fun r hr => ?_⟩
  have hQm : (nodePoly T).Monic := nodePoly_monic T
  have hQd : (nodePoly T).natDegree = T.card := nodePoly_natDegree T
  have hd0 : 0 < T.card := card_pos.mpr hne
  have hQ1 : nodePoly T ≠ 1 := fun h => by rw [h, natDegree_one] at hQd; omega
  have hRd := natDegree_modByMonic_lt ((X : ℤ[X]) ^ (r - 1)) hQm hQ1
  rw [hQd] at hRd
  have hRA := modByMonic_add_div ((X : ℤ[X]) ^ (r - 1)) (nodePoly T)
  obtain ⟨R, hR⟩ : ∃ R, R = (X : ℤ[X]) ^ (r - 1) %ₘ nodePoly T := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (X : ℤ[X]) ^ (r - 1) /ₘ nodePoly T := ⟨_, rfl⟩
  rw [← hR] at hRd hRA
  rw [← hA] at hRA
  have hev : ∀ z ∈ T, z ^ (r - 1) = R.eval z := by
    intro z hz'
    have := congrArg (eval z) hRA
    rw [eval_add, eval_mul, nodePoly_eval_node hz', zero_mul, add_zero, eval_pow, eval_X] at this
    exact this.symm
  have hmr : mom T a r = R.coeff 0 * mom T a 1 := by
    have h1 : mom T a r = ∑ z ∈ T, a z * z * R.eval z := by
      rw [mom]
      apply sum_congr rfl
      intro z hz'
      rw [← hev z hz', mul_assoc, ← pow_succ']
      have : r - 1 + 1 = r := by omega
      rw [this]
    rw [h1, sum_mul_eval T a R hRd]
    obtain ⟨d', hd'⟩ : ∃ d', T.card = d' + 1 := ⟨T.card - 1, by omega⟩
    rw [hd', sum_range_succ']
    rw [sum_eq_zero (fun i hi => by
      rw [hz (i + 1 + 1) (by omega) (by have := mem_range.mp hi; omega), mul_zero]), zero_add]
  have hR0 : R.coeff 0 = -((nodePoly T).coeff 0 * A.coeff 0) := by
    have := congrArg (coeff · 0) hRA
    simp only [coeff_add, mul_coeff_zero, coeff_X_pow] at this
    rw [if_neg (by omega)] at this
    linear_combination this
  rw [hmr, hR0]
  have : ∏ z ∈ T, z ∣ (nodePoly T).coeff 0 := by
    rw [nodePoly_coeff_zero, dvd_prod_neg_iff]
  obtain ⟨c, hc⟩ := this
  exact ⟨-(c * A.coeff 0), by rw [hc]; ring⟩

end Construct

/-! ## The moment target and the exact minimal node bounds -/

section Exact

variable (p : ℕ) [hp : Fact p.Prime]

/-- The moment form of target `D_k`: for some `v` and some `u` prime to `p`,
`s_1 = p^v u (mod p^(v+k))` and `s_r = 0 (mod p^(v+k))` for every `r >= 2`. -/
def MomentTarget (k : ℕ) (T : Finset ℤ) (a : ℤ → ℤ) : Prop :=
  ∃ v : ℕ, ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ^ (v + k) ∣ mom T a 1 - p ^ v * u ∧
    ∀ r, 2 ≤ r → (p : ℤ) ^ (v + k) ∣ mom T a r

/-- Lower bound in target form. -/
theorem momentTarget_le (k : ℕ) (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (a : ℤ → ℤ)
    (h : MomentTarget p k T a) : k ≤ ∑ z ∈ T, padicValInt p z := by
  obtain ⟨v, u, hu, h1, hr⟩ := h
  exact thmH_moment p T h0 a v k u hu h1 (fun r hr2 _ => hr r hr2)

/-- Every nonempty node set without `0` whose product is divisible by `p^k` carries weights
meeting the target. -/
theorem momentTarget_of_dvd (k : ℕ) (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (hne : T.Nonempty)
    (hk : (p : ℤ) ^ k ∣ ∏ z ∈ T, z) : ∃ a, MomentTarget p k T a := by
  obtain ⟨a, hC, hr⟩ := construct_moment T h0 hne
  set C := mom T a 1
  set v := padicValInt p C
  have hvC : (p : ℤ) ^ v ∣ C := padicValInt_dvd C
  refine ⟨a, v, C / p ^ v, ?_, ?_, ?_⟩
  · intro hu
    have h2 : (p : ℤ) ^ (v + 1) ∣ C := by
      rw [← Int.mul_ediv_cancel' hvC, pow_succ]; exact mul_dvd_mul_left _ hu
    rcases (padicValInt_dvd_iff (v + 1) C).1 h2 with h | h
    · exact hC h
    · omega
  · rw [Int.mul_ediv_cancel' hvC, sub_self]; exact dvd_zero _
  · intro r hr2
    rw [pow_add]
    exact (mul_dvd_mul hvC hk).trans (hr r hr2)

/-- **Exact cheap bound (moment level).** For `k >= 1`, weights on nodes in `{1..Z}` meet the
moment target iff `S(p^k) <= Z`. -/
theorem cheap_moment_iff {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    (∃ T ⊆ cheapNodes Z, ∃ a, MomentTarget p k T a) ↔ FrobLevel.kempner p k ≤ Z := by
  constructor
  · rintro ⟨T, hT, a, h⟩
    have h0 : (0 : ℤ) ∉ T := fun h => zero_not_mem_cheap Z (hT h)
    have h1 := momentTarget_le p k T h0 a h
    have h2 : ∑ z ∈ T, padicValInt p z ≤ ∑ z ∈ cheapNodes Z, padicValInt p z :=
      sum_le_sum_of_subset hT
    rw [sum_val_cheap] at h2
    exact FrobLevel.kempner_le p (h1.trans h2)
  · intro hZ
    have hZ1 : 1 ≤ Z := (FrobLevel.kempner_pos p hk).trans hZ
    refine ⟨cheapNodes Z, subset_refl _, momentTarget_of_dvd p k _ (zero_not_mem_cheap Z)
      ⟨1, by simp [cheapNodes]; omega⟩ ?_⟩
    rw [pow_dvd_prod_iff p _ (zero_not_mem_cheap Z), sum_val_cheap]
    exact kempner_dvd_factorial p hZ

/-- **Exact signed bound (moment level).** For `k >= 1`, weights on nodes in
`{-Z..-1} union {1..Z}` meet the moment target iff `S(p^ceil(k/2)) <= Z`. -/
theorem signed_moment_iff {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    (∃ T ⊆ signedNodes Z, ∃ a, MomentTarget p k T a) ↔
      FrobLevel.kempner p ((k + 1) / 2) ≤ Z := by
  constructor
  · rintro ⟨T, hT, a, h⟩
    have h0 : (0 : ℤ) ∉ T := fun h => zero_not_mem_signed Z (hT h)
    have h1 := momentTarget_le p k T h0 a h
    have h2 : ∑ z ∈ T, padicValInt p z ≤ ∑ z ∈ signedNodes Z, padicValInt p z :=
      sum_le_sum_of_subset hT
    rw [sum_val_signed] at h2
    exact FrobLevel.kempner_le p (by omega)
  · intro hZ
    have hZ1 : 1 ≤ Z := (FrobLevel.kempner_pos p (by omega)).trans hZ
    refine ⟨signedNodes Z, subset_refl _, momentTarget_of_dvd p k _ (zero_not_mem_signed Z)
      ⟨1, by simp [signedNodes]; omega⟩ ?_⟩
    rw [pow_dvd_prod_iff p _ (zero_not_mem_signed Z), sum_val_signed]
    have := kempner_dvd_factorial p hZ
    omega

/-- The least cheap node bound is `S(p^k)`. -/
theorem cheap_moment_isLeast {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | ∃ T ⊆ cheapNodes Z, ∃ a, MomentTarget p k T a} (FrobLevel.kempner p k) :=
  ⟨(cheap_moment_iff p hk _).2 le_rfl, fun _ hZ => (cheap_moment_iff p hk _).1 hZ⟩

/-- The least signed node bound is `S(p^ceil(k/2))`. -/
theorem signed_moment_isLeast {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | ∃ T ⊆ signedNodes Z, ∃ a, MomentTarget p k T a}
      (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨(signed_moment_iff p hk _).2 le_rfl, fun _ hZ => (signed_moment_iff p hk _).1 hZ⟩

end Exact

end M2L
