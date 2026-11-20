/-
Run r25 / M2, seat M2L2 (item 7): Theorems A, B, H and Corollary A1 with coefficients in a ring
`O` (covering cyclotomic coefficients and characters with cyclotomic values).

Setting: `O` a commutative domain of characteristic `0` (so torsion-free over `ℤ`) with
`p^m O ∩ ℤ = p^m ℤ` (`IntDvdDescends p O`, the "O cap Q = Z" line of the M2a / M2a-v reports).
`IntDvdDescends` holds for the ring of integers of every number field (`intDvdDescends_ringOfIntegers`),
in particular for cyclotomic integers. Degrees stay integers; coefficients, core values,
corrections and character values live in `O`. A unit modulo `p` is `UnitModP p u`:
`u w = 1 (mod p O)` for some `w` (no Frobenius, no field assumption on `O / p O`).

Contents.
1. `unit_lift`: a unit modulo `p` is a unit modulo `p^k`.
2. `thmH_moment_O` (Theorem H lower bound, moment form over `O`), `thmB_moment_O`,
   `thmB_moment_O_exists` (Theorem B), `momO_p_sub_one` (Fermat on the integer degrees).
3. The family over `O`: `famO`, `famO_slice` (Theorem A modulo `N O`), `TargetDO`,
   `thmH_O` (Theorem H lower bound for the family over `O`, several cores per degree, degree `0`,
   twists by congruence on an infinite prime set), `thmB_O_exists`, `corA1_O` (no member gives
   the prime indicator modulo `p O`).
4. `intDvdDescends_ringOfIntegers`: the hypothesis holds for `𝓞 K`, `K` any number field.

Lean v4.33.1 with Mathlib; imports the r25 library, round 1 and FamGen.
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

namespace M2L2

open Finset ArithmeticFunction M2L Polynomial
open scoped ArithmeticFunction.omega

section Ring

variable {O : Type*} [CommRing O]

/-- `p^m O ∩ ℤ = p^m ℤ`. -/
def IntDvdDescends (p : ℕ) (O : Type*) [CommRing O] : Prop :=
  ∀ (m : ℕ) (x : ℤ), (p : O) ^ m ∣ (x : O) → (p : ℤ) ^ m ∣ x

/-- `u` is a unit modulo `p O`. -/
def UnitModP (p : ℕ) (u : O) : Prop := ∃ w : O, (p : O) ∣ u * w - 1

/-- A unit modulo `p` is a unit modulo `p^k`. -/
theorem unit_lift {p : ℕ} {u : O} (hu : UnitModP p u) (k : ℕ) : ∃ w : O, (p : O) ^ k ∣ u * w - 1 := by
  obtain ⟨w, t, ht⟩ := hu
  set e := u * w - 1
  refine ⟨w * ∑ i ∈ range k, (-e) ^ i, ?_⟩
  have g := geom_sum_mul (-e) k
  have h : u * (w * ∑ i ∈ range k, (-e) ^ i) - 1 = -((-e) ^ k) := by
    have : u * w = 1 + e := by simp [e]
    rw [← mul_assoc, this]
    linear_combination (-1 : O) * g
  rw [h, ht]
  exact ⟨-((-t) ^ k), by ring⟩

/-- Moments over `O`: `s_r = sum over z in T of a z * z ^ r`. -/
def momO (T : Finset ℤ) (a : ℤ → O) (r : ℕ) : O := ∑ z ∈ T, a z * (z : O) ^ r

/-- The node-polynomial relation over `O`: `sum_(i <= d) q_i s_(i+1) = 0`. -/
theorem nodePoly_moment_rel_O (T : Finset ℤ) (a : ℤ → O) :
    ∑ i ∈ range (T.card + 1), ((nodePoly T).coeff i : O) * momO T a (i + 1) = 0 := by
  have hd : (nodePoly T).natDegree < T.card + 1 := by rw [nodePoly_natDegree]; omega
  have hev : ∀ z ∈ T, ∑ i ∈ range (T.card + 1), ((nodePoly T).coeff i : O) * (z : O) ^ i = 0 := by
    intro z hz
    have := congrArg (fun x : ℤ => (x : O)) (nodePoly_eval_node hz)
    simp only [eval_eq_sum_range' hd, Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_zero] at this
    exact this
  calc ∑ i ∈ range (T.card + 1), ((nodePoly T).coeff i : O) * momO T a (i + 1)
      = ∑ z ∈ T, a z * (z : O) *
          ∑ i ∈ range (T.card + 1), ((nodePoly T).coeff i : O) * (z : O) ^ i := by
        simp_rw [momO, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro z _; apply sum_congr rfl; intro i _; ring
    _ = 0 := sum_eq_zero fun z hz => by rw [hev z hz, mul_zero]

variable [IsDomain O] [CharZero O]

theorem natCast_pow_ne_zero (p : ℕ) [hp : Fact p.Prime] (m : ℕ) : (p : O) ^ m ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)

/-- **Theorem H, lower bound, over `O` (moment form).** Integer nodes `T` without `0`, weights in
`O`. If `s_1 = p^v u (mod p^(v+k) O)` with `u` a unit modulo `p`, and `s_r = 0 (mod p^(v+k) O)`
for `2 <= r <= |T| + 1`, then `k <= sum over z in T of v_p(z)`. -/
theorem thmH_moment_O (p : ℕ) [hp : Fact p.Prime] (hD : IntDvdDescends p O) (T : Finset ℤ)
    (h0 : (0 : ℤ) ∉ T) (a : ℤ → O) (v k : ℕ) (u : O) (hu : UnitModP p u)
    (h1 : (p : O) ^ (v + k) ∣ momO T a 1 - p ^ v * u)
    (hr : ∀ r, 2 ≤ r → r ≤ T.card + 1 → (p : O) ^ (v + k) ∣ momO T a r) :
    k ≤ ∑ z ∈ T, padicValInt p z := by
  have rel := nodePoly_moment_rel_O T a
  rw [sum_range_succ'] at rel
  set q0 := (nodePoly T).coeff 0
  have hrest : (p : O) ^ (v + k) ∣
      ∑ i ∈ range T.card, ((nodePoly T).coeff (i + 1) : O) * momO T a (i + 1 + 1) :=
    dvd_sum fun i hi => (hr _ (by omega) (by have := mem_range.mp hi; omega)).mul_left _
  have hq : (p : O) ^ (v + k) ∣ (q0 : O) * momO T a 1 := by
    have : (q0 : O) * momO T a 1 = -(∑ i ∈ range T.card,
        ((nodePoly T).coeff (i + 1) : O) * momO T a (i + 1 + 1)) := by
      simp only [zero_add] at rel; linear_combination rel
    rw [this]; exact hrest.neg_right
  have hq2 : (p : O) ^ v * (p : O) ^ k ∣ (p : O) ^ v * ((q0 : O) * u) := by
    rw [← pow_add]
    have := dvd_sub hq (h1.mul_left (q0 : O))
    have e : (q0 : O) * momO T a 1 - (q0 : O) * (momO T a 1 - p ^ v * u) =
        (p : O) ^ v * ((q0 : O) * u) := by ring
    rwa [e] at this
  have hq3 : (p : O) ^ k ∣ (q0 : O) * u :=
    (mul_dvd_mul_iff_left (natCast_pow_ne_zero p v)).1 hq2
  obtain ⟨w, hw⟩ := unit_lift hu k
  have hq4 : (p : O) ^ k ∣ (q0 : O) := by
    have := dvd_sub (hq3.mul_right w) (hw.mul_left (q0 : O))
    have e : (q0 : O) * u * w - (q0 : O) * (u * w - 1) = (q0 : O) := by ring
    rwa [e] at this
  have hq5 := hD k q0 hq4
  have hq0 : q0 = ∏ z ∈ T, -z := nodePoly_coeff_zero T
  rw [hq0, dvd_prod_neg_iff, pow_dvd_prod_iff p T h0] at hq5
  exact hq5

/-- **Theorem B over `O` (moment form, exact).** If `s_1 = p u (mod p^2 O)` and `s_r = 0
(mod p^2 O)` for one `r >= 2` with `p (p - 1) | r - 1`, then
`sum over nodes z with v_p(z) = 1 of a_z (z / p) = u (mod p O)`. -/
theorem thmB_moment_O (p : ℕ) [hp : Fact p.Prime] (T : Finset ℤ) (a : ℤ → O) (u : O) {r : ℕ}
    (hr2 : 2 ≤ r) (hr : p * (p - 1) ∣ r - 1) (h1 : (p : O) ^ 2 ∣ momO T a 1 - p * u)
    (hs : (p : O) ^ 2 ∣ momO T a r) :
    (p : O) ∣ ∑ z ∈ val1 p T, a z * ((z / p : ℤ) : O) - u := by
  have hsum : (p : O) ^ 2 ∣ (momO T a 1 - momO T a r) -
      ∑ z ∈ T, a z * (((if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0 : ℤ)) : O) := by
    have e : (momO T a 1 - momO T a r) -
        ∑ z ∈ T, a z * (((if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0 : ℤ)) : O) =
        ∑ z ∈ T, a z * ((((z - z ^ r) -
          (if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0) : ℤ)) : O) := by
      simp only [momO, pow_one, ← sum_sub_distrib]
      apply sum_congr rfl; intro z _; push_cast; ring
    rw [e]
    refine dvd_sum fun z _ => Dvd.dvd.mul_left ?_ _
    obtain ⟨m, hm⟩ := node_congr p z hr2 hr
    rw [hm]; push_cast; exact dvd_mul_right _ _
  have hfilt : ∑ z ∈ T, a z * (((if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0 : ℤ)) : O) =
      (p : O) * ∑ z ∈ val1 p T, a z * ((z / p : ℤ) : O) := by
    have : ∀ z ∈ T, a z * (((if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then z else 0 : ℤ)) : O) =
        if (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z then a z * (z : O) else 0 := by
      intro z _; split_ifs <;> simp
    rw [sum_congr rfl this, ← sum_filter, Finset.mul_sum, val1]
    apply sum_congr rfl
    intro z hz
    have hpz := ((mem_filter.mp hz).2).1
    have : (z : O) = (p : O) * ((z / p : ℤ) : O) := by
      rw [← Int.mul_ediv_cancel' hpz]; push_cast; rw [Int.mul_ediv_cancel' hpz]
    rw [this]; ring
  rw [hfilt] at hsum
  have key : (p : O) * (p : O) ∣ (p : O) * (∑ z ∈ val1 p T, a z * ((z / p : ℤ) : O) - u) := by
    have := dvd_sub (dvd_sub h1 hs) hsum
    have e : momO T a 1 - p * u - momO T a r - (momO T a 1 - momO T a r -
        (p : O) * ∑ z ∈ val1 p T, a z * ((z / p : ℤ) : O)) =
        (p : O) * (∑ z ∈ val1 p T, a z * ((z / p : ℤ) : O) - u) := by ring
    rw [← pow_two]; rwa [e] at this
  exact (mul_dvd_mul_iff_left (Nat.cast_ne_zero.mpr hp.out.ne_zero)).1 key

/-- **Theorem B over `O` (existence).** If moreover `u` is a unit modulo `p`, some node `z` with
`v_p(z) = 1` has `a_z` not in `p O`. -/
theorem thmB_moment_O_exists (p : ℕ) [hp : Fact p.Prime] (hD : IntDvdDescends p O)
    (T : Finset ℤ) (a : ℤ → O) (u : O) (hu : UnitModP p u) {r : ℕ} (hr2 : 2 ≤ r)
    (hr : p * (p - 1) ∣ r - 1) (h1 : (p : O) ^ 2 ∣ momO T a 1 - p * u)
    (hs : (p : O) ^ 2 ∣ momO T a r) :
    ∃ z ∈ T, (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧ ¬ (p : O) ∣ a z := by
  by_contra hne
  push Not at hne
  have hall : (p : O) ∣ ∑ z ∈ val1 p T, a z * ((z / p : ℤ) : O) := dvd_sum fun z hz => by
    have hz' := mem_filter.mp hz
    exact (hne z hz'.1 hz'.2.1 hz'.2.2).mul_right _
  have hpu : (p : O) ∣ u := by
    have := dvd_sub hall (thmB_moment_O p T a u hr2 hr h1 hs)
    rwa [sub_sub_cancel] at this
  obtain ⟨w, hw⟩ := hu
  have h1' : (p : O) ^ 1 ∣ ((1 : ℤ) : O) := by
    have := dvd_sub (hpu.mul_right w) hw
    rw [sub_sub_cancel] at this; simpa using this
  have := hD 1 1 h1'
  rw [pow_one] at this
  exact (int_prime p).not_dvd_one this

omit [IsDomain O] [CharZero O] in
/-- Fermat on integer degrees, over `O`: `s_p = s_1 (mod p O)`. -/
theorem momO_p_sub_one (p : ℕ) [hp : Fact p.Prime] (T : Finset ℤ) (a : ℤ → O) :
    (p : O) ∣ momO T a p - momO T a 1 := by
  rw [momO, momO, ← sum_sub_distrib]
  refine dvd_sum fun z _ => ?_
  obtain ⟨m, hm⟩ := fermat_int_aux p z
  rw [pow_one, ← mul_sub]
  refine Dvd.dvd.mul_left ?_ _
  have : (z : O) ^ p - (z : O) = ((z ^ p - z : ℤ) : O) := by push_cast; ring
  rw [this, hm]; push_cast; exact dvd_mul_right _ _
where
  fermat_int_aux (p : ℕ) [Fact p.Prime] (z : ℤ) : (p : ℤ) ∣ z ^ p - z := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]

end Ring

/-! ## The family over `O` -/

section FamO

variable {O : Type*} [CommRing O] {ι : Type*}

/-- The family member over `O`: `sum over i in I of c i * (G i * h i)`. -/
def famO (I : Finset ι) (c : ι → O) (G h : ι → ArithmeticFunction O) : ArithmeticFunction O :=
  ⟨fun n => ∑ i ∈ I, c i * (G i * h i) n, by simp⟩

/-- Aggregated weight on degree `z`: `sum over i with deg i = z of c i * h i 1`. -/
def wtO (I : Finset ι) (deg : ι → ℤ) (c : ι → O) (h : ι → ArithmeticFunction O) (z : ℤ) : O :=
  ∑ i ∈ I with deg i = z, c i * h i 1

theorem momO_wtO (I : Finset ι) (deg : ι → ℤ) (c : ι → O) (h : ι → ArithmeticFunction O)
    (r : ℕ) : momO (I.image deg) (wtO I deg c h) r = ∑ i ∈ I, c i * h i 1 * (deg i : O) ^ r := by
  rw [momO, ← Finset.sum_fiberwise_of_maps_to (t := I.image deg) (g := deg)
    (fun i hi => mem_image_of_mem deg hi)]
  apply sum_congr rfl
  intro z _
  rw [wtO, Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

theorem momO_erase_zero (T : Finset ℤ) (a : ℤ → O) {r : ℕ} (hr : r ≠ 0) :
    momO (T.erase 0) a r = momO T a r := by
  unfold momO
  exact Finset.sum_erase T (by rw [Int.cast_zero, zero_pow hr, mul_zero])

/-- **Slice formula over `O` (Theorem A).** For squarefree `n` with `G i (q) = deg i (mod x O)`
at its prime factors and `h i = 0 (mod x O)` on squarefree `m > 1`:
`famO n = sum over degrees z of wtO_z z ^ omega(n) (mod x O)`. -/
theorem famO_slice (x : O) (I : Finset ι) (deg : ι → ℤ) (c : ι → O)
    (G h : ι → ArithmeticFunction O)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → q ∣ n → x ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → x ∣ h i m) :
    x ∣ famO I c G h n - momO (I.image deg) (wtO I deg c h) (ω n) := by
  rw [momO_wtO]
  let φ := Ideal.Quotient.mk (Ideal.span {x})
  have hφ : ∀ a b : O, x ∣ a - b ↔ φ a = φ b := fun a b => by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  rw [hφ]
  show φ (∑ i ∈ I, c i * (G i * h i) n) = φ (∑ i ∈ I, c i * h i 1 * (deg i : O) ^ ω n)
  rw [map_sum, map_sum]
  apply sum_congr rfl
  intro i hi
  have h1 : φ ((G i * h i) n) =
      (FrobLevel.Dir.mapHom φ (G i) * FrobLevel.Dir.mapHom φ (h i)) n := by
    rw [← map_mul]; rfl
  have hh' : ∀ m, Squarefree m → 1 < m → FrobLevel.Dir.mapHom φ (h i) m = 0 := by
    intro m hm hm1
    rw [FrobLevel.Dir.mapHom_apply]
    exact (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (hh i hi m hm hm1)
  have hG' : ∀ q, q.Prime → q ∣ n → FrobLevel.Dir.mapHom φ (G i) q = φ (deg i) := by
    intro q hq hqn
    rw [FrobLevel.Dir.mapHom_apply]
    exact ((hφ _ _).1 (hGq i hi q hq hqn))
  rw [map_mul, h1, mul_apply_squarefree _ _ hn hh',
    apply_squarefree_of_mult (isMultiplicative_mapHom φ (hG i hi)) hn hG',
    FrobLevel.Dir.mapHom_apply, map_mul, map_mul, map_pow]
  ring

variable [IsDomain O] [CharZero O]

/-- Target `D_k` over `O`: at every prime `q`, `f q = p^v u_q (mod p^(v+k) O)` with `u_q` a unit
modulo `p`; `f n = 0 (mod p^(v+k) O)` whenever `omega(n) >= 2`. -/
def TargetDO (p v k : ℕ) (f : ArithmeticFunction O) : Prop :=
  (∀ q : ℕ, q.Prime → ∃ u : O, UnitModP p u ∧ (p : O) ^ (v + k) ∣ f q - p ^ v * u) ∧
    ∀ n : ℕ, 2 ≤ ω n → (p : O) ^ (v + k) ∣ f n

omit [IsDomain O] [CharZero O] in
/-- The moment target from `TargetDO` along an infinite prime set. -/
theorem moments_of_targetDO (p : ℕ) {v k : ℕ} (I : Finset ι) (deg : ι → ℤ) (c : ι → O)
    (G h : ι → ArithmeticFunction O) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : O) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ^ (v + k) ∣ h i m)
    (hf : TargetDO p v k (famO I c G h)) :
    (∃ u : O, UnitModP p u ∧
      (p : O) ^ (v + k) ∣ momO (I.image deg) (wtO I deg c h) 1 - p ^ v * u) ∧
    ∀ r, 2 ≤ r → (p : O) ^ (v + k) ∣ momO (I.image deg) (wtO I deg c h) r := by
  have hsl : ∀ n, Squarefree n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : O) ^ (v + k) ∣ famO I c G h n - momO (I.image deg) (wtO I deg c h) (ω n) :=
    fun n hn hnP => famO_slice _ I deg c G h hG hn
      (fun i hi q hq hqn => hGq i hi q (hnP q hq hqn)) hh
  constructor
  · obtain ⟨q, hqP⟩ := hP.nonempty
    have hq := hPp q hqP
    obtain ⟨u, hu, hfu⟩ := hf.1 q hq
    have hs := hsl q hq.prime.irreducible.squarefree (fun q' hq' hq'q => by
      rw [(Nat.prime_dvd_prime_iff_eq hq' hq).1 hq'q]; exact hqP)
    rw [cardDistinctFactors_apply_prime hq] at hs
    refine ⟨u, hu, ?_⟩
    have := dvd_sub hfu hs
    rwa [sub_sub_sub_cancel_left] at this
  · intro r hr
    obtain ⟨n, hn, hnr, hnP⟩ := exists_slice P hP hPp r
    have hs := hsl n hn hnP
    rw [hnr] at hs
    have := dvd_sub (hf.2 n (hnr ▸ hr)) hs
    rwa [sub_sub_cancel] at this

/-- **Theorem H, lower bound, over `O` (family).** Cores and corrections with values in `O`
(for example characters with cyclotomic values), several cores per degree, degree `0` allowed.
If `famO I c G h` meets `TargetDO p v k`, then `k <= sum over nonzero degrees z of v_p(z)`. -/
theorem thmH_O (p : ℕ) [hp : Fact p.Prime] (hD : IntDvdDescends p O) {v k : ℕ} (I : Finset ι)
    (deg : ι → ℤ) (c : ι → O) (G h : ι → ArithmeticFunction O) (P : Set ℕ) (hP : P.Infinite)
    (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : O) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ^ (v + k) ∣ h i m)
    (hf : TargetDO p v k (famO I c G h)) :
    k ≤ ∑ z ∈ (I.image deg).erase 0, padicValInt p z := by
  obtain ⟨⟨u, hu, h1⟩, hr⟩ := moments_of_targetDO p I deg c G h P hP hPp hG hGq hh hf
  refine thmH_moment_O p hD _ (Finset.notMem_erase 0 _) (wtO I deg c h) v k u hu ?_
    (fun r hr2 _ => ?_)
  · rwa [momO_erase_zero _ _ one_ne_zero]
  · rw [momO_erase_zero _ _ (by omega)]; exact hr r hr2

/-- **Theorem B over `O` (family).** Under target D over `O` (`TargetDO p 1 1`), some degree `z`
with `v_p(z) = 1` has aggregated weight not in `p O`. -/
theorem thmB_O_exists (p : ℕ) [hp : Fact p.Prime] (hD : IntDvdDescends p O) (I : Finset ι)
    (deg : ι → ℤ) (c : ι → O) (G h : ι → ArithmeticFunction O) (P : Set ℕ) (hP : P.Infinite)
    (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : O) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ^ 2 ∣ h i m)
    (hf : TargetDO p 1 1 (famO I c G h)) :
    ∃ z ∈ I.image deg, (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧ ¬ (p : O) ∣ wtO I deg c h z := by
  obtain ⟨⟨u, hu, h1⟩, hr⟩ := moments_of_targetDO p I deg c G h P hP hPp hG hGq hh hf
  have h2 := hp.out.two_le
  have hr1 : 1 ≤ p * (p - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact thmB_moment_O_exists p hD _ _ u hu (r := 1 + p * (p - 1)) (by omega) (by simp)
    (by simpa using h1) (hr _ (by omega))

omit [IsDomain O] [CharZero O] in
/-- **Corollary A1 over `O` (family).** Cores `deg i (mod p O)` on an infinite prime set,
corrections `0 (mod p O)` on squarefree `m > 1`: a value at one prime of `P` that is a unit modulo
`p`, together with `f n = 0 (mod p O)` on squarefree `n` with `omega(n) >= 2` and prime factors in
`P`, is impossible. (Fermat is applied to the integer degrees only; `O / p O` need not be a field.) -/
theorem corA1_O (p : ℕ) [hp : Fact p.Prime] (hD : IntDvdDescends p O) (I : Finset ι)
    (deg : ι → ℤ) (c : ι → O) (G h : ι → ArithmeticFunction O) (P : Set ℕ) (hP : P.Infinite)
    (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : O) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ∣ h i m)
    {q : ℕ} (hqP : q ∈ P) (hunit : UnitModP p (famO I c G h q))
    (hcomp : ∀ n, Squarefree n → 2 ≤ ω n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : O) ∣ famO I c G h n) : False := by
  have hsl : ∀ n, Squarefree n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : O) ∣ famO I c G h n - momO (I.image deg) (wtO I deg c h) (ω n) :=
    fun n hn hnP => famO_slice _ I deg c G h hG hn
      (fun i hi q hq hqn => hGq i hi q (hnP q hq hqn)) hh
  obtain ⟨n, hn, hnr, hnP⟩ := exists_slice P hP hPp p
  have hqq := hPp q hqP
  have h1 := hsl q hqq.prime.irreducible.squarefree (fun q' hq' hq'q => by
    rw [(Nat.prime_dvd_prime_iff_eq hq' hqq).1 hq'q]; exact hqP)
  rw [cardDistinctFactors_apply_prime hqq] at h1
  have h2 := hsl n hn hnP
  rw [hnr] at h2
  have h3 := momO_p_sub_one p (I.image deg) (wtO I deg c h)
  have hfn := hcomp n hn (by rw [hnr]; exact hp.out.two_le) hnP
  have hfq : (p : O) ∣ famO I c G h q := by
    have := dvd_add (dvd_sub (dvd_sub hfn h2) h3) h1
    have e : famO I c G h n - (famO I c G h n - momO (I.image deg) (wtO I deg c h) p) -
        (momO (I.image deg) (wtO I deg c h) p - momO (I.image deg) (wtO I deg c h) 1) +
        (famO I c G h q - momO (I.image deg) (wtO I deg c h) 1) = famO I c G h q := by ring
    rwa [e] at this
  obtain ⟨w, hw⟩ := hunit
  have h1' : (p : O) ^ 1 ∣ ((1 : ℤ) : O) := by
    have := dvd_sub (hfq.mul_right w) hw
    rw [sub_sub_cancel] at this; simpa using this
  have := hD 1 1 h1'
  rw [pow_one] at this
  exact (int_prime p).not_dvd_one this

end FamO

/-! ## The hypothesis holds for rings of integers -/

open NumberField in
/-- **`p^m 𝓞_K ∩ ℤ = p^m ℤ`** for every number field `K` (in particular cyclotomic fields). -/
theorem intDvdDescends_ringOfIntegers (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    IntDvdDescends p (𝓞 K) := by
  intro m x hx
  rcases eq_or_ne p 0 with rfl | hp0
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [Nat.cast_zero, zero_pow hm] at hx ⊢
      have : ((x : 𝓞 K)) = 0 := zero_dvd_iff.mp hx
      exact zero_dvd_iff.mpr (by exact_mod_cast this)
  obtain ⟨y, hy⟩ := hx
  -- the rational `x / p^m` is integral over `ℤ`
  set r : ℚ := (x : ℚ) / (p : ℚ) ^ m
  have hpm : (p : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp0)
  have hry : algebraMap ℚ K r = (y : K) := by
    have := congrArg (fun t : 𝓞 K => (t : K)) hy
    simp only [map_intCast, map_mul, map_pow, map_natCast] at this
    have hyK : (x : K) = (p : K) ^ m * (y : K) := by
      rw [RingOfIntegers.coe_eq_algebraMap y]; exact this
    have hpK : ((p : K)) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp0)
    rw [show r = (x : ℚ) / (p : ℚ) ^ m from rfl, map_div₀, map_pow, map_intCast, map_natCast, hyK]
    field_simp
  have hint : IsIntegral ℤ r := by
    have hyi : IsIntegral ℤ (y : K) := y.isIntegral_coe
    rw [← hry] at hyi
    exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp hyi
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨n, ?_⟩
  have : (x : ℚ) = (p : ℚ) ^ m * n := by
    rw [show ((algebraMap ℤ ℚ) n) = (n : ℚ) by simp] at hn
    rw [hn]; simp only [r]; field_simp
  exact_mod_cast this

open NumberField in
/-- **Theorem H lower bound with cyclotomic coefficients.** `O = 𝓞 (ℚ(zeta_N))`. -/
theorem thmH_cyclotomic (N : ℕ) [NeZero N] (p : ℕ) [hp : Fact p.Prime] {ι : Type*} {v k : ℕ}
    (I : Finset ι) (deg : ι → ℤ) (c : ι → 𝓞 (CyclotomicField N ℚ))
    (G h : ι → ArithmeticFunction (𝓞 (CyclotomicField N ℚ))) (P : Set ℕ) (hP : P.Infinite)
    (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : 𝓞 (CyclotomicField N ℚ)) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : 𝓞 (CyclotomicField N ℚ)) ^ (v + k) ∣ h i m)
    (hf : TargetDO p v k (famO I c G h)) :
    k ≤ ∑ z ∈ (I.image deg).erase 0, padicValInt p z :=
  thmH_O p (intDvdDescends_ringOfIntegers _ p) I deg c G h P hP hPp hG hGq hh hf

end M2L2
