module

public import Mathlib
public import Construct

/-!
  Seat M2L4, item 4: (H5) explicit Lagrange weights; the coefficient tables of A19 section 11, each
  row checked by kernel `decide` on concrete integers and turned into an explicit TargetD member;
  the level table (H1)/(H2) evaluated; and (H6)/(H7) as identities of formal power series over Z.
-/

@[expose] public section

open Finset Polynomial
open scoped Nat

namespace M2L4
open M2L

/-! ## 1. (H5): Lagrange weights at zero -/

/-- `L_z(0) = ∏_{t ∈ T, t ≠ z} (-t) / (z - t)`, computed in `ℚ`. -/
noncomputable def lag0 (T : Finset ℤ) (z : ℤ) : ℚ := ∏ t ∈ T.erase z, (-(t : ℚ)) / ((z : ℚ) - t)

lemma intCast_injOn (T : Finset ℤ) : Set.InjOn (fun z : ℤ => (z : ℚ)) (T : Set ℤ) :=
  fun _ _ _ _ h => by simpa using h

lemma cast_ne_zero_of_mem {T : Finset ℤ} (h0 : (0 : ℤ) ∉ T) {z : ℤ} (hz : z ∈ T) : (z : ℚ) ≠ 0 := by
  intro h; apply h0; have : z = 0 := by exact_mod_cast h
  exact this ▸ hz

lemma basis_eval_zero (T : Finset ℤ) (z : ℤ) :
    (Lagrange.basis T (fun t : ℤ => (t : ℚ)) z).eval 0 = lag0 T z := by
  rw [Lagrange.basis, eval_prod, lag0]
  refine prod_congr rfl fun t _ => ?_
  rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, zero_sub]
  ring

/-- Lagrange interpolation at `0`: `f(0) = ∑_{z ∈ T} f(z) L_z(0)` when `deg f < |T|`. -/
theorem lagrange_at_zero (T : Finset ℤ) (f : ℚ[X]) (hf : f.degree < T.card) :
    f.eval 0 = ∑ z ∈ T, f.eval (z : ℚ) * lag0 T z := by
  have h := Lagrange.eq_interpolate (s := T) (v := fun t : ℤ => (t : ℚ)) (intCast_injOn T) hf
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun z _ => ?_
  rw [eval_mul, eval_C, basis_eval_zero]

/-- **(H5)**: with `a_z = C L_z(0) / z` on a node set `T` without `0`,
`s_1 = ∑ a_z z = C` and `s_r = ∑ a_z z^r = 0` for `2 ≤ r ≤ |T|`. -/
theorem H5_moments (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (C : ℚ) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ T.card) :
    ∑ z ∈ T, (C * lag0 T z / z) * (z : ℚ) ^ r = if r = 1 then C else 0 := by
  have hdeg : ((X : ℚ[X]) ^ (r - 1)).degree < T.card := by
    rw [degree_X_pow]; exact_mod_cast (by omega : r - 1 < T.card)
  have h := lagrange_at_zero T _ hdeg
  simp only [eval_pow, eval_X] at h
  have e : ∀ z ∈ T, (C * lag0 T z / z) * (z : ℚ) ^ r = C * ((z : ℚ) ^ (r - 1) * lag0 T z) := by
    intro z hz
    have hz0 : (z : ℚ) ≠ 0 := cast_ne_zero_of_mem h0 hz
    have : (z : ℚ) ^ r = (z : ℚ) * (z : ℚ) ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; field_simp
  rw [sum_congr rfl e, ← mul_sum, ← h]
  split_ifs with h1
  · subst h1; simp
  · rw [zero_pow (by omega), mul_zero]

/-- Uniqueness: weights with vanishing moments `s_1, ..., s_{|T|}` on a node set without `0`
are zero. -/
theorem weights_unique (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (b : ℤ → ℚ)
    (hb : ∀ r, 1 ≤ r → r ≤ T.card → ∑ z ∈ T, b z * (z : ℚ) ^ r = 0) : ∀ z ∈ T, b z = 0 := by
  intro z0 hz0
  set P : ℚ[X] := X * Lagrange.basis T (fun t : ℤ => (t : ℚ)) z0
  have hPdeg : P.natDegree < T.card + 1 := by
    have h1 : P.natDegree ≤ (X : ℚ[X]).natDegree
        + (Lagrange.basis T (fun t : ℤ => (t : ℚ)) z0).natDegree := natDegree_mul_le
    rw [Lagrange.natDegree_basis (intCast_injOn T) hz0, natDegree_X] at h1
    have : 0 < T.card := card_pos.2 ⟨z0, hz0⟩
    omega
  have hev : ∀ z ∈ T, P.eval (z : ℚ) = if z = z0 then (z0 : ℚ) else 0 := by
    intro z hz
    simp only [P, eval_mul, eval_X]
    by_cases h : z = z0
    · subst h; rw [Lagrange.eval_basis_self (intCast_injOn T) hz, mul_one, ite_eq_left rfl]
    · rw [Lagrange.eval_basis_of_ne (s := T) (v := fun t : ℤ => (t : ℚ)) (Ne.symm h) hz, mul_zero,
        ite_eq_right h]
  have hsum : ∑ z ∈ T, b z * P.eval (z : ℚ) = 0 := by
    simp_rw [eval_eq_sum_range' hPdeg, mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine sum_eq_zero fun z _ => ?_
      simp [P]
    · have := hb i hi0 (by have := mem_range.1 hi; omega)
      rw [show ∑ z ∈ T, b z * (P.coeff i * (z : ℚ) ^ i) = P.coeff i * ∑ z ∈ T, b z * (z : ℚ) ^ i by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring, this, mul_zero]
  rw [sum_congr rfl (fun z hz => by rw [hev z hz])] at hsum
  simp only [mul_ite, mul_zero, sum_ite_eq', ite_eq_left hz0] at hsum
  exact (mul_eq_zero.1 hsum).resolve_right (cast_ne_zero_of_mem h0 hz0)

/-- Weights with `s_1 = C` and `s_r = 0` for `2 ≤ r ≤ |T|` are exactly the explicit Lagrange
weights `C L_z(0) / z` of (H5). -/
theorem weights_eq_lagrange (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (a : ℤ → ℤ) (C : ℤ)
    (h1 : mom T a 1 = C) (hr : ∀ r, 2 ≤ r → r ≤ T.card → mom T a r = 0) :
    ∀ z ∈ T, (a z : ℚ) = C * lag0 T z / z := by
  have := weights_unique T h0 (fun z => (a z : ℚ) - C * lag0 T z / z) (fun r hr1 hrT => by
    simp only [sub_mul, sum_sub_distrib]
    rw [H5_moments T h0 (C : ℚ) hr1 hrT]
    have hm : ∑ z ∈ T, (a z : ℚ) * (z : ℚ) ^ r = ((mom T a r : ℤ) : ℚ) := by
      simp [mom]
    rw [hm]
    split_ifs with h
    · subst h; rw [h1]; ring
    · rw [hr r (by omega) hrT]; simp)
  intro z hz
  exact sub_eq_zero.1 (this z hz)

/-! ## 2. All composite moments are multiples of `C ∏ z` -/

/-- If `s_r = 0` for `2 ≤ r ≤ |T|`, then `s_1 ∏_{z ∈ T} z ∣ s_r` for every `r ≥ 2`
(the monic node-polynomial recurrence). -/
theorem mom_dvd_of_vanish (T : Finset ℤ) (hne : T.Nonempty) (a : ℤ → ℤ)
    (hz : ∀ r, 2 ≤ r → r ≤ T.card → mom T a r = 0) {r : ℕ} (hr : 2 ≤ r) :
    mom T a 1 * ∏ z ∈ T, z ∣ mom T a r := by
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
    rw [ite_eq_right (by omega)] at this
    linear_combination this
  rw [hmr, hR0]
  have : ∏ z ∈ T, z ∣ (nodePoly T).coeff 0 := by
    rw [nodePoly_coeff_zero, dvd_prod_neg_iff]
  obtain ⟨c, hc⟩ := this
  exact ⟨-(c * A.coeff 0), by rw [hc]; ring⟩

/-- A table row gives an explicit TargetD member: `F = fam T a zpowZeta hcorr`, i.e.
`F = ∑_z a_z (d_z * h_z)`, has `F(n) = s_{ω(n)}`. If `s_1 = p^v u` with `p ∤ u` and
`p^(v+k) ∣ s_1 ∏ z`, then `F` meets `TargetD p v k`. -/
theorem row_targetD (p : ℕ) [Fact p.Prime] (T : Finset ℤ) (hne : T.Nonempty) (a : ℤ → ℤ)
    (hz : ∀ r, 2 ≤ r → r ≤ T.card → mom T a r = 0) {v k : ℕ} (u : ℤ)
    (hC : mom T a 1 = (p : ℤ) ^ v * u) (hu : ¬ (p : ℤ) ∣ u)
    (hk : (p : ℤ) ^ (v + k) ∣ mom T a 1 * ∏ z ∈ T, z) :
    TargetD p v k (fam T a zpowZeta hcorr) := by
  refine ⟨fun q hq => ⟨u, hu, ?_⟩, fun n hn => ?_⟩
  · rw [fam_hcorr_apply T a hq.ne_zero, ArithmeticFunction.cardDistinctFactors_apply_prime hq, hC,
      sub_self]
    exact dvd_zero _
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [fam_hcorr_apply T a hn0]
    exact hk.trans (mom_dvd_of_vanish T hne a hz hn)

/-! ## 3. The coefficient tables, row by row -/

/-- Weights read from a list of `(node, weight)` pairs (`0` off the list). -/
def wOf (l : List (ℤ × ℤ)) (z : ℤ) : ℤ := (l.lookup z).getD 0

def P2 : ℤ → ℤ := wOf [(1, 4), (2, -1)]
def P3 : ℤ → ℤ := wOf [(1, 18), (2, -9), (3, 2)]
def P4 : ℤ → ℤ := wOf [(1, 48), (2, -36), (3, 16), (4, -3)]
def P6 : ℤ → ℤ := wOf [(1, 360), (2, -450), (3, 400), (4, -225), (5, 72), (6, -10)]
def P9 : ℤ → ℤ := wOf [(1, 22680), (2, -45360), (3, 70560), (4, -79380), (5, 63504), (6, -35280),
  (7, 12960), (8, -2835), (9, 280)]
def S2 : ℤ → ℤ := wOf [(-2, 1), (-1, -8), (1, 8), (2, -1)]
def S3 : ℤ → ℤ := wOf [(-3, -1), (-2, 9), (-1, -45), (1, 45), (2, -9), (3, 1)]
def S4 : ℤ → ℤ := wOf [(-4, 3), (-3, -32), (-2, 168), (-1, -672), (1, 672), (2, -168), (3, 32),
  (4, -3)]
def S6 : ℤ → ℤ := wOf [(-6, 5), (-5, -72), (-4, 495), (-3, -2200), (-2, 7425), (-1, -23760),
  (1, 23760), (2, -7425), (3, 2200), (4, -495), (5, 72), (6, -5)]

/-- A row is checked: `s_1 = C` and `s_r = 0` for `2 ≤ r ≤ |T|`. -/
def RowOK (T : Finset ℤ) (a : ℤ → ℤ) (C : ℤ) : Prop :=
  mom T a 1 = C ∧ ∀ r ∈ Icc 2 T.card, mom T a r = 0

lemma card_cheap (Z : ℕ) : (cheapNodes Z).card = Z := by simp [cheapNodes]

lemma card_signed (Z : ℕ) : (signedNodes Z).card = 2 * Z := by
  rw [signedNodes, card_union_of_disjoint]
  · simp; omega
  · rw [disjoint_left]; intro z h1 h2; simp at h1 h2; omega

/-- **Positive-node rows** (`T = {1..Z}`), each checked by kernel `decide`. -/
theorem rows_positive :
    RowOK (cheapNodes 2) P2 2 ∧ RowOK (cheapNodes 3) P3 6 ∧ RowOK (cheapNodes 4) P4 12 ∧
    RowOK (cheapNodes 6) P6 60 ∧ RowOK (cheapNodes 9) P9 2520 := by
  simp only [RowOK, card_cheap]
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Signed-node rows** (`T = {-Z..-1} ∪ {1..Z}`, weights in the stated node order), each checked
by kernel `decide`. -/
theorem rows_signed :
    RowOK (signedNodes 2) S2 12 ∧ RowOK (signedNodes 3) S3 60 ∧ RowOK (signedNodes 4) S4 840 ∧
    RowOK (signedNodes 6) S6 27720 := by
  simp only [RowOK, card_signed]
  refine ⟨by decide, by decide, by decide, by decide⟩

lemma RowOK.vanish {T : Finset ℤ} {a : ℤ → ℤ} {C : ℤ} (h : RowOK T a C) :
    ∀ r, 2 ≤ r → r ≤ T.card → mom T a r = 0 :=
  fun r h2 h3 => h.2 r (mem_Icc.2 ⟨h2, h3⟩)

/-- Every table row is the explicit (H5) Lagrange weight vector `a_z = C L_z(0) / z`. -/
theorem rows_are_lagrange :
    (∀ z ∈ cheapNodes 2, (P2 z : ℚ) = 2 * lag0 (cheapNodes 2) z / z) ∧
    (∀ z ∈ cheapNodes 3, (P3 z : ℚ) = 6 * lag0 (cheapNodes 3) z / z) ∧
    (∀ z ∈ cheapNodes 4, (P4 z : ℚ) = 12 * lag0 (cheapNodes 4) z / z) ∧
    (∀ z ∈ cheapNodes 6, (P6 z : ℚ) = 60 * lag0 (cheapNodes 6) z / z) ∧
    (∀ z ∈ cheapNodes 9, (P9 z : ℚ) = 2520 * lag0 (cheapNodes 9) z / z) ∧
    (∀ z ∈ signedNodes 2, (S2 z : ℚ) = 12 * lag0 (signedNodes 2) z / z) ∧
    (∀ z ∈ signedNodes 3, (S3 z : ℚ) = 60 * lag0 (signedNodes 3) z / z) ∧
    (∀ z ∈ signedNodes 4, (S4 z : ℚ) = 840 * lag0 (signedNodes 4) z / z) ∧
    (∀ z ∈ signedNodes 6, (S6 z : ℚ) = 27720 * lag0 (signedNodes 6) z / z) := by
  obtain ⟨p2, p3, p4, p6, p9⟩ := rows_positive
  obtain ⟨s2, s3, s4, s6⟩ := rows_signed
  have hc := zero_not_mem_cheap
  have hs := zero_not_mem_signed
  exact ⟨by exact_mod_cast weights_eq_lagrange _ (hc 2) P2 2 p2.1 p2.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hc 3) P3 6 p3.1 p3.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hc 4) P4 12 p4.1 p4.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hc 6) P6 60 p6.1 p6.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hc 9) P9 2520 p9.1 p9.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hs 2) S2 12 s2.1 s2.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hs 3) S3 60 s3.1 s3.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hs 4) S4 840 s4.1 s4.vanish,
    by exact_mod_cast weights_eq_lagrange _ (hs 6) S6 27720 s6.1 s6.vanish⟩

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

lemma cheap_nonempty (Z : ℕ) (hZ : 1 ≤ Z) : (cheapNodes Z).Nonempty :=
  ⟨1, by simp [cheapNodes]; omega⟩

lemma signed_nonempty (Z : ℕ) (hZ : 1 ≤ Z) : (signedNodes Z).Nonempty :=
  ⟨1, by simp [signedNodes]; omega⟩

/-- **The rows as explicit TargetD members** (`F = ∑_z a_z (d_z * h_z)`, value `C` at every
prime power), at the levels used by the level table:
positive rows: `Z = 2`: `p = 2, k = 1`; `Z = 3`: `p = 3, k = 1`; `Z = 4`: `p = 2, k = 3`;
`Z = 6`: `p = 2, k = 4` and `p = 3, k = 2`; `Z = 9`: `p = 3, k = 4`.
Signed rows: `Z = 2`: `p = 2, k = 2`; `Z = 3`: `p = 3, k = 2`; `Z = 4`: `p = 2, k = 6`;
`Z = 6`: `p = 3, k = 4`. -/
theorem rows_targetD :
    TargetD 2 1 1 (fam (cheapNodes 2) P2 zpowZeta hcorr) ∧
    TargetD 3 1 1 (fam (cheapNodes 3) P3 zpowZeta hcorr) ∧
    TargetD 2 2 3 (fam (cheapNodes 4) P4 zpowZeta hcorr) ∧
    TargetD 2 2 4 (fam (cheapNodes 6) P6 zpowZeta hcorr) ∧
    TargetD 3 1 2 (fam (cheapNodes 6) P6 zpowZeta hcorr) ∧
    TargetD 3 2 4 (fam (cheapNodes 9) P9 zpowZeta hcorr) ∧
    TargetD 2 2 2 (fam (signedNodes 2) S2 zpowZeta hcorr) ∧
    TargetD 3 1 2 (fam (signedNodes 3) S3 zpowZeta hcorr) ∧
    TargetD 2 3 6 (fam (signedNodes 4) S4 zpowZeta hcorr) ∧
    TargetD 3 2 4 (fam (signedNodes 6) S6 zpowZeta hcorr) := by
  obtain ⟨p2, p3, p4, p6, p9⟩ := rows_positive
  obtain ⟨s2, s3, s4, s6⟩ := rows_signed
  refine ⟨row_targetD 2 _ (cheap_nonempty 2 (by norm_num)) P2 p2.vanish 1 (by rw [p2.1]; norm_num)
      (by decide) (by rw [p2.1]; decide),
    row_targetD 3 _ (cheap_nonempty 3 (by norm_num)) P3 p3.vanish 2 (by rw [p3.1]; norm_num)
      (by decide) (by rw [p3.1]; decide),
    row_targetD 2 _ (cheap_nonempty 4 (by norm_num)) P4 p4.vanish 3 (by rw [p4.1]; norm_num)
      (by decide) (by rw [p4.1]; decide),
    row_targetD 2 _ (cheap_nonempty 6 (by norm_num)) P6 p6.vanish 15 (by rw [p6.1]; norm_num)
      (by decide) (by rw [p6.1]; decide),
    row_targetD 3 _ (cheap_nonempty 6 (by norm_num)) P6 p6.vanish 20 (by rw [p6.1]; norm_num)
      (by decide) (by rw [p6.1]; decide),
    row_targetD 3 _ (cheap_nonempty 9 (by norm_num)) P9 p9.vanish 280 (by rw [p9.1]; norm_num)
      (by decide) (by rw [p9.1]; decide),
    row_targetD 2 _ (signed_nonempty 2 (by norm_num)) S2 s2.vanish 3 (by rw [s2.1]; norm_num)
      (by decide) (by rw [s2.1]; decide),
    row_targetD 3 _ (signed_nonempty 3 (by norm_num)) S3 s3.vanish 20 (by rw [s3.1]; norm_num)
      (by decide) (by rw [s3.1]; decide),
    row_targetD 2 _ (signed_nonempty 4 (by norm_num)) S4 s4.vanish 105 (by rw [s4.1]; norm_num)
      (by decide) (by rw [s4.1]; decide),
    row_targetD 3 _ (signed_nonempty 6 (by norm_num)) S6 s6.vanish 3080 (by rw [s6.1]; norm_num)
      (by decide) (by rw [s6.1]; decide)⟩

/-! ## 4. The level table (H1), (H2) -/

lemma kempner_eq_of (p : ℕ) [Fact p.Prime] {k N : ℕ} (hN : 0 < N) (h1 : p ^ k ∣ N !)
    (h2 : ¬ p ^ k ∣ (N - 1)!) : FrobLevel.kempner p k = N := by
  unfold FrobLevel.kempner
  rw [Nat.find_eq_iff]
  refine ⟨h1, fun m hm hd => h2 (hd.trans (Nat.factorial_dvd_factorial (by omega)))⟩

lemma k21 : FrobLevel.kempner 2 1 = 2 := kempner_eq_of 2 (by norm_num) (by decide) (by decide)
lemma k22 : FrobLevel.kempner 2 2 = 4 := kempner_eq_of 2 (by norm_num) (by decide) (by decide)
lemma k23 : FrobLevel.kempner 2 3 = 4 := kempner_eq_of 2 (by norm_num) (by decide) (by decide)
lemma k24 : FrobLevel.kempner 2 4 = 6 := kempner_eq_of 2 (by norm_num) (by decide) (by decide)
lemma k31 : FrobLevel.kempner 3 1 = 3 := kempner_eq_of 3 (by norm_num) (by decide) (by decide)
lemma k32 : FrobLevel.kempner 3 2 = 6 := kempner_eq_of 3 (by norm_num) (by decide) (by decide)
lemma k33 : FrobLevel.kempner 3 3 = 9 := kempner_eq_of 3 (by norm_num) (by decide) (by decide)
lemma k34 : FrobLevel.kempner 3 4 = 9 := kempner_eq_of 3 (by norm_num) (by decide) (by decide)

/-- **The table of A19 section 11**: `Z_signed(p,k) = S(p^⌈k/2⌉)` and `Z_cheap(p,k) = S(p^k)` for
`p = 2, 3`, `k = 1..4` (each Kempner value from `p^k ∣ N!` and `p^k ∤ (N-1)!` by `decide`). -/
theorem level_table :
    (FrobLevel.kempner 2 ((1 + 1) / 2), FrobLevel.kempner 2 ((2 + 1) / 2),
      FrobLevel.kempner 2 ((3 + 1) / 2), FrobLevel.kempner 2 ((4 + 1) / 2)) = (2, 2, 4, 4) ∧
    (FrobLevel.kempner 2 1, FrobLevel.kempner 2 2, FrobLevel.kempner 2 3,
      FrobLevel.kempner 2 4) = (2, 4, 4, 6) ∧
    (FrobLevel.kempner 3 ((1 + 1) / 2), FrobLevel.kempner 3 ((2 + 1) / 2),
      FrobLevel.kempner 3 ((3 + 1) / 2), FrobLevel.kempner 3 ((4 + 1) / 2)) = (3, 3, 6, 6) ∧
    (FrobLevel.kempner 3 1, FrobLevel.kempner 3 2, FrobLevel.kempner 3 3,
      FrobLevel.kempner 3 4) = (3, 6, 9, 9) := by
  norm_num [k21, k22, k23, k24, k31, k32, k33, k34]

/-- With round 1's exact bounds (`Zcheap_eq`, `Zsigned_eq`), every cell of the table is the least
achievable `Z`. -/
theorem level_table_isLeast :
    IsLeast {Z | SignedAchievable 2 1 Z} 2 ∧ IsLeast {Z | SignedAchievable 2 2 Z} 2 ∧
    IsLeast {Z | SignedAchievable 2 3 Z} 4 ∧ IsLeast {Z | SignedAchievable 2 4 Z} 4 ∧
    IsLeast {Z | CheapAchievable 2 1 Z} 2 ∧ IsLeast {Z | CheapAchievable 2 2 Z} 4 ∧
    IsLeast {Z | CheapAchievable 2 3 Z} 4 ∧ IsLeast {Z | CheapAchievable 2 4 Z} 6 ∧
    IsLeast {Z | SignedAchievable 3 1 Z} 3 ∧ IsLeast {Z | SignedAchievable 3 2 Z} 3 ∧
    IsLeast {Z | SignedAchievable 3 3 Z} 6 ∧ IsLeast {Z | SignedAchievable 3 4 Z} 6 ∧
    IsLeast {Z | CheapAchievable 3 1 Z} 3 ∧ IsLeast {Z | CheapAchievable 3 2 Z} 6 ∧
    IsLeast {Z | CheapAchievable 3 3 Z} 9 ∧ IsLeast {Z | CheapAchievable 3 4 Z} 9 := by
  have s : ∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k → FrobLevel.kempner p ((k + 1) / 2) = N →
      IsLeast {Z | SignedAchievable p k Z} N := fun p _ k N hk h => h ▸ Zsigned_eq p hk
  have c : ∀ (p : ℕ) [Fact p.Prime] (k N : ℕ), 1 ≤ k → FrobLevel.kempner p k = N →
      IsLeast {Z | CheapAchievable p k Z} N := fun p _ k N hk h => h ▸ Zcheap_eq p hk
  exact ⟨s 2 1 2 le_rfl k21, s 2 2 2 (by norm_num) k21, s 2 3 4 (by norm_num) k22,
    s 2 4 4 (by norm_num) k22, c 2 1 2 le_rfl k21, c 2 2 4 (by norm_num) k22,
    c 2 3 4 (by norm_num) k23, c 2 4 6 (by norm_num) k24, s 3 1 3 le_rfl k31,
    s 3 2 3 (by norm_num) k31, s 3 3 6 (by norm_num) k32, s 3 4 6 (by norm_num) k32,
    c 3 1 3 le_rfl k31, c 3 2 6 (by norm_num) k32, c 3 3 9 (by norm_num) k33,
    c 3 4 9 (by norm_num) k34⟩

/-! ## 5. (H6), (H7) as formal power series identities over `ℤ` -/

section Series

/-- `(1 - t)⁻¹ = ∑ t^n` in `ℤ⟦t⟧`. -/
noncomputable abbrev geomS : PowerSeries ℤ := PowerSeries.invUnitsSub 1

lemma geomS_coeff (n : ℕ) : PowerSeries.coeff n geomS = 1 := by
  simp [geomS, PowerSeries.coeff_invUnitsSub]

lemma geomS_mul : geomS * (1 - PowerSeries.X) = 1 := by
  have := PowerSeries.invUnitsSub_mul_sub (1 : ℤˣ)
  simpa using this

/-- `1 - t` as a unit of `ℤ⟦t⟧`. -/
noncomputable def oneSubX : (PowerSeries ℤ)ˣ :=
  ⟨1 - PowerSeries.X, geomS, by rw [mul_comm]; exact geomS_mul, geomS_mul⟩

lemma oneSubX_inv : ((oneSubX⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = geomS := rfl

/-- The local series of `h_z` in (H6): `(1 + (z-1) t)(1 - t)^(z-1)`, for every integer `z`
(negative exponents through the unit `1 - t`); its coefficients are integers by construction. -/
noncomputable def H6series (z : ℤ) : PowerSeries ℤ :=
  (1 + PowerSeries.C (z - 1) * PowerSeries.X) * ((oneSubX ^ (z - 1) : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

/-- **(H7) locally**: `(H6 series) · (1 - t)^(-z) = 1 + z t / (1 - t)` for every integer `z`. -/
theorem H7_series (z : ℤ) :
    H6series z * ((oneSubX ^ (-z) : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      = 1 + PowerSeries.C z * PowerSeries.X * geomS := by
  have hu : ((oneSubX ^ (z - 1) : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      * ((oneSubX ^ (-z) : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = geomS := by
    rw [← Units.val_mul, ← zpow_add, show z - 1 + -z = -1 by ring, zpow_neg_one]; rfl
  have hinv : (1 - PowerSeries.X) * geomS = 1 := by rw [mul_comm]; exact geomS_mul
  rw [H6series, mul_assoc, hu]
  have e : (1 + PowerSeries.C (z - 1) * PowerSeries.X : PowerSeries ℤ)
      = (1 - PowerSeries.X) + PowerSeries.C z * PowerSeries.X := by
    rw [map_sub, map_one]; ring
  rw [e, add_mul, hinv]

/-- The coefficients of `1 + z t / (1 - t)`: `1` at `t^0` and `z` at every `t^e`, `e ≥ 1`
(the local values of `B_z = z^ω`). -/
theorem B_series_coeff (z : ℤ) (e : ℕ) :
    PowerSeries.coeff e (1 + PowerSeries.C z * PowerSeries.X * geomS)
      = if e = 0 then 1 else z := by
  rcases e with _ | e
  · simp
  · rw [mul_comm (PowerSeries.C z), mul_assoc, map_add, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, geomS_coeff]
    simp

/-- The constant coefficient of the (H6) series is `1` and its linear coefficient is `0`,
for every integer `z` (so `h_z` is supported on squarefull integers). -/
theorem H6_coeff_zero_one (z : ℤ) :
    PowerSeries.coeff 0 (H6series z) = 1 ∧ PowerSeries.coeff 1 (H6series z) = 0 := by
  have hU : H6series z = (1 + PowerSeries.C z * PowerSeries.X * geomS)
      * ((oneSubX ^ z : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) := by
    rw [← H7_series z, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, mul_one]
  have step : ∀ (W V : (PowerSeries ℤ)ˣ) (c d : ℤ), PowerSeries.coeff 0 (W : PowerSeries ℤ) = 1 →
      PowerSeries.coeff 1 (W : PowerSeries ℤ) = c → PowerSeries.coeff 0 (V : PowerSeries ℤ) = 1 →
      PowerSeries.coeff 1 (V : PowerSeries ℤ) = d →
      PowerSeries.coeff 0 ((W * V : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 ∧
      PowerSeries.coeff 1 ((W * V : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = c + d := by
    intro W V c d hW0 hW1 hV0 hV1
    rw [Units.val_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    simp [Finset.Nat.antidiagonal_succ, hW0, hW1, hV0, hV1]
    ring
  have h0 : PowerSeries.coeff 0 ((oneSubX : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 ∧
      PowerSeries.coeff 1 ((oneSubX : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = -1 := by
    simp [oneSubX]
  have hi : PowerSeries.coeff 0 ((oneSubX⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 ∧
      PowerSeries.coeff 1 ((oneSubX⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    rw [oneSubX_inv, geomS_coeff, geomS_coeff]; exact ⟨rfl, rfl⟩
  have hz : ∀ n : ℤ, PowerSeries.coeff 0 ((oneSubX ^ n : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 ∧
      PowerSeries.coeff 1 ((oneSubX ^ n : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = -n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ m ih =>
      rw [zpow_add_one]
      have := step _ _ _ _ ih.1 ih.2 h0.1 h0.2
      exact ⟨this.1, by rw [this.2]; ring⟩
    | pred m ih =>
      rw [zpow_sub_one]
      have := step _ _ _ _ ih.1 ih.2 hi.1 hi.2
      exact ⟨this.1, by rw [this.2]; ring⟩
  obtain ⟨u0, u1⟩ := hz z
  have b0 : PowerSeries.coeff 0 (1 + PowerSeries.C z * PowerSeries.X * geomS) = 1 := by
    rw [B_series_coeff, ite_eq_left rfl]
  have b1 : PowerSeries.coeff 1 (1 + PowerSeries.C z * PowerSeries.X * geomS) = z := by
    rw [B_series_coeff, ite_eq_right one_ne_zero]
  generalize (1 + PowerSeries.C z * PowerSeries.X * geomS) = B at hU b0 b1
  rw [hU, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  constructor
  · simp [u0, b0]
  · simp [Finset.Nat.antidiagonal_succ, u0, u1, b0, b1]

end Series

end M2L4
