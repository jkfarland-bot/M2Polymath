/-
Run r25 / M2, seat M2L2 (item 2): the corollaries of Theorem B (A19, Q2 section 3) and the
Vandermonde variant of O2 (ledger R-113).

Target D is `TargetD p 1 1` (round 1): prime values `p u_q (mod p^2)` with `p` not dividing `u_q`,
values `0 (mod p^2)` on `omega >= 2`. All results are for the general family of FamGen (several
cores per degree, degree `0` allowed, twists by congruence on an infinite prime set `P`).

Contents.
1. `thmB_degree_p`: with unsigned degrees in `{0..p}`, target D forces degree `p` to occur, with
   aggregated weight prime to `p`. `not_targetD_below_p`: with unsigned degrees in `{0..p-1}`
   target D is impossible. `thmB_degree_pm_p`: signed degrees in `{-p..p}` force `p` or `-p`.
2. Modulo 9 (`p = 3`, degrees `0, 1, 2, 3`): `mod9_moment` (moments `r = 1, 2, 3` force
   `a_1 = a_2 = 0 (mod 9)` and `a_3 = u (mod 3)`); `mod9_I` (family: target D forces
   `9 | a_1`, `9 | a_2`, `3` not dividing `a_3`; `a_0` free); `mod9_iff` (the explicit members
   `a_1 B_1 + a_2 B_2 + a_3 B_3`: target D holds iff `9 | a_1`, `9 | a_2`, `3` does not divide `a_3`).
3. Vandermonde variant: `vandermonde_moment` (nodes in `{1..p-1}`: `s_1 = p u (mod p^2)`, `p` not
   dividing `u`, and `s_r = 0 (mod p^2)` for `2 <= r <= p` is impossible) and `vandermonde_I`
   (family, degrees in `{0..p-1}`: it suffices to know `f n = 0 (mod p^2)` on squarefree `n` with
   `2 <= omega(n) <= p` and prime factors in `P`).

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

open Finset ArithmeticFunction M2L
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

section DegP

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*}

/-- **Degree `p` is needed (unsigned).** Degrees in `{0..p}`: target D forces some index of degree
`p`, and the aggregated weight on degree `p` is prime to `p`. -/
theorem thmB_degree_p (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime) (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ p)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m)
    (hf : TargetD p 1 1 (famI I c G h)) :
    (p : ℤ) ∈ I.image deg ∧ ¬ (p : ℤ) ∣ wt I deg (aggI c h) p := by
  obtain ⟨z, hz, hpz, hp2z, hw⟩ := thmB_I_exists p I deg c G h P hP hPp hG hGq hh hf
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  have hzp : deg i = p := by
    obtain ⟨m, hm⟩ := hpz
    have h0 := hd i hi
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have hm0 : m ≠ 0 := by
      rintro rfl; rw [mul_zero] at hm; exact hp2z (hm ▸ dvd_zero _)
    have hm1 : m = 1 := by
      rcases lt_trichotomy m 1 with h | h | h
      · have : m < 0 := by omega
        nlinarith
      · exact h
      · nlinarith
    rw [hm, hm1, mul_one]
  rw [hzp] at hz hw
  exact ⟨hz, hw⟩

/-- **Degrees `1..p-1` do not suffice.** With unsigned degrees in `{0..p-1}` no member of the
family meets target D. -/
theorem not_targetD_below_p (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ p - 1)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m) :
    ¬ TargetD p 1 1 (famI I c G h) := by
  intro hf
  have hd' : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ p := fun i hi => ⟨(hd i hi).1, (hd i hi).2.trans
    (by linarith)⟩
  obtain ⟨hz, _⟩ := thmB_degree_p p I deg c G h P hP hPp hd' hG hGq hh hf
  obtain ⟨i, hi, he⟩ := mem_image.mp hz
  have := (hd i hi).2
  rw [he] at this
  linarith

/-- **Signed form.** Degrees in `{-p..p}`: target D forces degree `p` or `-p` to carry an aggregated
weight prime to `p`. -/
theorem thmB_degree_pm_p (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hd : ∀ i ∈ I, -(p : ℤ) ≤ deg i ∧ deg i ≤ p)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m)
    (hf : TargetD p 1 1 (famI I c G h)) :
    ∃ z ∈ I.image deg, (z = p ∨ z = -p) ∧ ¬ (p : ℤ) ∣ wt I deg (aggI c h) z := by
  obtain ⟨z, hz, hpz, hp2z, hw⟩ := thmB_I_exists p I deg c G h P hP hPp hG hGq hh hf
  refine ⟨z, hz, ?_, hw⟩
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  obtain ⟨m, hm⟩ := hpz
  have h0 := hd i hi
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [mul_zero] at hm; exact hp2z (hm ▸ dvd_zero _)
  have : m = 1 ∨ m = -1 := by
    rcases lt_trichotomy m 1 with h | h | h
    · rcases lt_trichotomy m (-1) with h' | h' | h'
      · nlinarith
      · exact Or.inr h'
      · omega
    · exact Or.inl h
    · nlinarith
  rcases this with h1 | h1
  · left; rw [hm, h1, mul_one]
  · right; rw [hm, h1]; ring

end DegP

/-! ## Modulo 9 -/

section Mod9

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Moments on `{0, 1, 2, 3}` for `r >= 1`. -/
theorem mom_0123 (a : ℤ → ℤ) {r : ℕ} (hr : r ≠ 0) :
    mom {0, 1, 2, 3} a r = a 1 + a 2 * 2 ^ r + a 3 * 3 ^ r := by
  simp [mom, zero_pow hr]
  ring

/-- **Modulo 9, moment level.** If `s_1 = 3 u`, `s_2 = s_3 = 0 (mod 9)` on degrees `{1, 2, 3}`
(degree `0` free), then `a_1 = a_2 = 0 (mod 9)` and `a_3 = u (mod 3)`. -/
theorem mod9_moment (a : ℤ → ℤ) (u : ℤ) (h1 : (9 : ℤ) ∣ mom {0, 1, 2, 3} a 1 - 3 * u)
    (h2 : (9 : ℤ) ∣ mom {0, 1, 2, 3} a 2) (h3 : (9 : ℤ) ∣ mom {0, 1, 2, 3} a 3) :
    (9 : ℤ) ∣ a 1 ∧ (9 : ℤ) ∣ a 2 ∧ (3 : ℤ) ∣ a 3 - u := by
  rw [mom_0123 a one_ne_zero] at h1
  rw [mom_0123 a two_ne_zero] at h2
  rw [mom_0123 a (by norm_num)] at h3
  norm_num at h1 h2 h3
  omega

variable {ι : Type*}

/-- **Modulo 9 (family).** `p = 3`, degrees in `{0, 1, 2, 3}` (several cores per degree allowed,
twists by congruence mod 9 on an infinite prime set): target D (`TargetD 3 1 1`, i.e. prime values
`3 u (mod 9)`, `3` not dividing `u`, and `0 (mod 9)` on `omega >= 2`) forces the aggregated weights
to satisfy `a_1 = a_2 = 0 (mod 9)` and `a_3` prime to `3`. -/
theorem mod9_I (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime) (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ 3)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (3 : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (3 : ℤ) ^ 2 ∣ h i m)
    (hf : TargetD 3 1 1 (famI I c G h)) :
    (9 : ℤ) ∣ wt I deg (aggI c h) 1 ∧ (9 : ℤ) ∣ wt I deg (aggI c h) 2 ∧
      ¬ (3 : ℤ) ∣ wt I deg (aggI c h) 3 := by
  obtain ⟨⟨u, hu, h1⟩, hr⟩ := moments_of_targetD_I 3 I deg c G h P hP hPp hG hGq hh hf
  have hsub : I.image deg ⊆ {0, 1, 2, 3} := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    have := hd i hi
    have : deg i = 0 ∨ deg i = 1 ∨ deg i = 2 ∨ deg i = 3 := by omega
    simp only [mem_insert, mem_singleton]; exact this
  have hm : ∀ r, mom (I.image deg) (wt I deg (aggI c h)) r = mom {0, 1, 2, 3}
      (wt I deg (aggI c h)) r := mom_subset hsub _ (fun z _ hz => wt_of_not_mem I deg _ hz)
  rw [hm] at h1
  have h2 := hr 2 le_rfl
  have h3 := hr 3 (by norm_num)
  rw [hm] at h2 h3
  norm_num at h1 h2 h3
  obtain ⟨e1, e2, e3⟩ := mod9_moment _ u h1 h2 h3
  refine ⟨e1, e2, fun h3' => hu ?_⟩
  have := dvd_sub h3' e3
  rwa [sub_sub_cancel] at this

theorem wt_id (T : Finset ℤ) (b : ℤ → ℤ) (z : ℤ) : wt T id b z = if z ∈ T then b z else 0 := by
  rw [wt]
  simp only [id]
  rw [Finset.sum_filter, Finset.sum_ite_eq']

/-- **Modulo 9, explicit members (iff).** For `F = a_1 B_1 + a_2 B_2 + a_3 B_3` (round 1's
`fam {1, 2, 3} a zpowZeta hcorr`, `B_z(n) = z ^ omega(n)`): target D holds iff `9 | a_1`,
`9 | a_2` and `3` does not divide `a_3`. -/
theorem mod9_iff (a : ℤ → ℤ) :
    TargetD 3 1 1 (fam {1, 2, 3} a zpowZeta hcorr) ↔
      (9 : ℤ) ∣ a 1 ∧ (9 : ℤ) ∣ a 2 ∧ ¬ (3 : ℤ) ∣ a 3 := by
  constructor
  · intro hf
    rw [fam_eq_famI] at hf
    have := mod9_I ({1, 2, 3} : Finset ℤ) id a zpowZeta hcorr {q | q.Prime}
      Nat.infinite_setOfPred_prime (fun _ hq => hq)
      (fun i hi => by simp at hi; simp [id]; omega) (fun z _ => zpowZeta_mult z)
      (fun z _ q hq => by rw [zpowZeta_prime z hq, id, sub_self]; exact dvd_zero _)
      (fun z _ m hm hm1 => by rw [hcorr_squarefree z hm hm1]; exact dvd_zero _) hf
    simp only [wt_id, aggI, hcorr_one, mul_one] at this
    simpa using this
  · rintro ⟨h1, h2, h3⟩
    have hval : ∀ n, n ≠ 0 → fam {1, 2, 3} a zpowZeta hcorr n =
        a 1 + a 2 * 2 ^ ω n + a 3 * 3 ^ ω n := by
      intro n hn
      rw [fam_hcorr_apply _ _ hn]
      simp [mom]
      ring
    refine ⟨fun q hq => ⟨a 3 + (a 1 + 2 * a 2) / 3, by omega, ?_⟩, fun n hn => ?_⟩
    · rw [hval q hq.ne_zero, cardDistinctFactors_apply_prime hq]
      norm_num
      omega
    · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      rw [hval n hn0]
      obtain ⟨r, hr⟩ : ∃ r, ω n = r + 2 := ⟨ω n - 2, by omega⟩
      rw [hr, pow_add, pow_add]
      norm_num
      obtain ⟨x, hx⟩ := h1
      obtain ⟨y, hy⟩ := h2
      exact ⟨x + y * 2 ^ r * 4 + a 3 * 3 ^ r, by rw [hx, hy]; ring⟩

end Mod9

/-! ## The Vandermonde variant (R-113): unsigned degrees `1..p-1`, moments `r <= p` -/

section Vandermonde

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*}

theorem sum_val_below_p (T : Finset ℤ) (hT : T ⊆ cheapNodes (p - 1)) :
    ∑ z ∈ T, padicValInt p z = 0 := by
  apply sum_eq_zero
  intro z hz
  have := hT hz
  simp only [cheapNodes, mem_Icc] at this
  apply padicValInt.eq_zero_of_not_dvd
  rintro ⟨m, hm⟩
  have hp1 := hp.out.two_le
  have hp0 : (0 : ℤ) < p := by omega
  rcases lt_trichotomy m 0 with h | h | h
  · nlinarith
  · rw [h] at hm; omega
  · have : (p : ℤ) ≤ z := by rw [hm]; nlinarith
    omega

omit hp in
theorem card_le_below_p (T : Finset ℤ) (hT : T ⊆ cheapNodes (p - 1)) : T.card ≤ p - 1 := by
  have := card_le_card hT
  rwa [cheapNodes, Int.card_Icc, show ((p - 1 : ℕ) : ℤ) + 1 - 1 = ((p - 1 : ℕ) : ℤ) by ring,
    Int.toNat_natCast] at this

/-- **Vandermonde variant (moment level).** Nodes in `{1..p-1}`: `s_1 = p u (mod p^2)` with `p`
not dividing `u` and `s_r = 0 (mod p^2)` for every `2 <= r <= p` cannot both hold. -/
theorem vandermonde_moment (T : Finset ℤ) (hT : T ⊆ cheapNodes (p - 1)) (a : ℤ → ℤ) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (h1 : (p : ℤ) ^ 2 ∣ mom T a 1 - p * u)
    (hr : ∀ r, 2 ≤ r → r ≤ p → (p : ℤ) ^ 2 ∣ mom T a r) : False := by
  have hcard := card_le_below_p p T hT
  have h0 : (0 : ℤ) ∉ T := fun h => zero_not_mem_cheap _ (hT h)
  have := thmH_moment p T h0 a 1 1 u hu (by simpa using h1)
    (fun r hr2 hr3 => by simpa using hr r hr2 (by have := hp.out.two_le; omega))
  rw [sum_val_below_p p T hT] at this
  omega

/-- **Vandermonde variant (family, finite range).** Degrees in `{0..p-1}`, cores `deg i (mod p^2)`
on an infinite prime set `P`, corrections `0 (mod p^2)` on squarefree `m > 1`. A prime `q` in `P`
with `f q = p u (mod p^2)`, `p` not dividing `u`, and `f n = 0 (mod p^2)` on every squarefree `n`
with `2 <= omega(n) <= p` and prime factors in `P`, cannot both hold. -/
theorem vandermonde_I (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ p - 1)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m)
    {q : ℕ} (hqP : q ∈ P) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (hfq : (p : ℤ) ^ 2 ∣ famI I c G h q - p * u)
    (hcomp : ∀ n, Squarefree n → 2 ≤ ω n → ω n ≤ p → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : ℤ) ^ 2 ∣ famI I c G h n) : False := by
  have hsl : ∀ n, Squarefree n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : ℤ) ^ 2 ∣ famI I c G h n - mom (I.image deg) (wt I deg (aggI c h)) (ω n) := by
    intro n hn hnP
    have := famI_slice (p ^ 2) I deg c G h hG hn
      (fun i hi q hq hqn => by push_cast; exact hGq i hi q (hnP q hq hqn))
      (fun i hi m hm hm1 => by push_cast; exact hh i hi m hm hm1)
    push_cast at this; exact this
  have hq := hPp q hqP
  have hs1 := hsl q hq.prime.irreducible.squarefree (fun q' hq' hq'q => by
    rw [(Nat.prime_dvd_prime_iff_eq hq' hq).1 hq'q]; exact hqP)
  rw [cardDistinctFactors_apply_prime hq] at hs1
  have hd' : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ ((p - 1 : ℕ) : ℤ) := fun i hi => by
    have := hd i hi
    push_cast [Nat.cast_sub (by have := hp.out.two_le; omega : 1 ≤ p)]
    exact this
  refine vandermonde_moment p _ (erase_subset_cheap hd') (wt I deg (aggI c h)) u hu ?_ ?_
  · rw [mom_erase_zero _ _ one_ne_zero]
    have := dvd_sub hfq hs1
    rwa [sub_sub_sub_cancel_left] at this
  · intro r hr2 hrp
    rw [mom_erase_zero _ _ (by omega)]
    obtain ⟨n, hn, hnr, hnP⟩ := exists_slice P hP hPp r
    have hs := hsl n hn hnP
    rw [hnr] at hs
    have := dvd_sub (hcomp n hn (hnr ▸ hr2) (hnr ▸ hrp) hnP) hs
    rwa [sub_sub_cancel] at this

end Vandermonde

end M2L2
