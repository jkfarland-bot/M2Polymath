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
import BCor
import Twist
import Summatory
import MuShift
import RingO
import TwistO

namespace AuditV2

open Finset ArithmeticFunction M2L M2L2
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## A1: the prime indicator modulo p^k meets TargetU, so not_targetU rules it out. -/

def primeInd : ArithmeticFunction ℤ := ⟨fun n => if n.Prime then 1 else 0, by simp [Nat.not_prime_zero]⟩

theorem primeInd_targetU (p : ℕ) [Fact p.Prime] (k : ℕ) : TargetU p k primeInd := by
  refine ⟨fun q hq => ?_, fun n hn h2 => ?_⟩
  · show (p : ℤ) ^ k ∣ (if q.Prime then 1 else 0) - 1
    simp [hq]
  · have : ¬ n.Prime := fun hp => by
      rw [cardDistinctFactors_apply_prime hp] at h2; omega
    show (p : ℤ) ^ k ∣ (if n.Prime then 1 else 0)
    simp [this]

/-- Any untwisted integral family member differs from the prime indicator modulo p^k, k >= 1. -/
example (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) {ι : Type*} (I : Finset ι) (deg : ι → ℤ)
    (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) :
    ¬ (∀ n, (p : ℤ) ^ k ∣ famI I c G h n - primeInd n) := by
  intro hall
  apply not_targetU_untwisted p hk I deg c G h hG hGq hh
  obtain ⟨h1, h2⟩ := primeInd_targetU p k
  refine ⟨fun q hq => ?_, fun n hn hn2 => ?_⟩
  · have := dvd_add (hall q) (h1 q hq); ring_nf at this ⊢; simpa [sub_eq_add_neg] using this
  · have := dvd_add (hall n) (h2 n hn hn2); simpa using this

/-- The (B_p - delta)/p example is not an integral family member (combining the two A1 results). -/
example (p : ℕ) [Fact p.Prime] {ι : Type*} (I : Finset ι) (deg : ι → ℤ)
    (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) :
    famI I c G h ≠ Ediv p := by
  intro e
  exact not_targetU_untwisted p le_rfl I deg c G h hG hGq hh (e ▸ (Bp_sub_delta p).2.2)

/-! ## BCor: mod9_iff is satisfiable and sharp. -/

example : TargetD 3 1 1 (fam {1, 2, 3} (fun z => if z = 3 then 1 else 0) zpowZeta hcorr) :=
  (mod9_iff _).2 (by decide)

example : ¬ TargetD 3 1 1 (fam {1, 2, 3} (fun z => if z = 3 then 1 else if z = 1 then 3 else 0)
    zpowZeta hcorr) := fun h => by
  have := ((mod9_iff _).1 h).1; revert this; decide

/-! ## Twist: the signed bound in the paper's measure (|signed degree| <= Z, not factor count)
follows from signedI_lower with the twisted prime set. -/

theorem signed_twisted_lower_sdeg (p : ℕ) [hp : Fact p.Prime] {ι : Type*} {v k Z : ℕ}
    (I : Finset ι) (L : ι → List TwFactor) (c : ι → ℤ)
    (h : ι → ArithmeticFunction ℤ) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hd : ∀ i ∈ I, |sdeg (L i)| ≤ Z)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c (fun i => core (L i)) h)) :
    FrobLevel.kempner p ((k + 1) / 2) ≤ Z :=
  signedI_lower p I (fun i => sdeg (L i)) c (fun i => core (L i)) h
    (primesOneMod (twModulus p (v + k) I L))
    (primesOneMod_infinite (twModulus_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i hi => abs_le.mp (hd i hi)) (fun i _ => core_mult (L i))
    (core_congr_pow p (v + k)) hh hf

/-! ## Twist non-vacuity: a member built from twisted-core lists meets TargetD 2 1 1. -/

theorem ell_one_zero_eq : ell (1 : DirichletCharacter ℤ 1) 0 = (ζ : ArithmeticFunction ℤ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ell_trivial_apply 0 hn, pow_zero, natCoe_apply, zeta_apply_ne hn, Nat.cast_one]

theorem core_two : core [powF 0 false, powF 0 false] = zpowZeta 2 := by
  have : (powF 0 false).af = (ζ : ArithmeticFunction ℤ) := by
    simp only [TwFactor.af, powF, Bool.false_eq_true, if_false]; exact ell_one_zero_eq
  rw [zpowZeta_of_pos (by norm_num)]
  simp [core, this, pow_two]

example : TargetD 2 1 1 (famI ({0} : Finset ℕ) (fun _ => 1)
    (fun _ => core [powF 0 false, powF 0 false]) (fun _ => hcorr 2)) := by
  have hv : ∀ n, n ≠ 0 → famI ({0} : Finset ℕ) (fun _ => 1)
      (fun _ => core [powF 0 false, powF 0 false]) (fun _ => hcorr 2) n = 2 ^ ω n := by
    intro n hn
    rw [famI_apply, sum_singleton, core_two, core_mul_hcorr, Bz_apply 2 hn, one_mul]
  refine ⟨fun q hq => ⟨1, by decide, ?_⟩, fun n hn => ?_⟩
  · rw [hv q hq.ne_zero, cardDistinctFactors_apply_prime hq]; norm_num
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [hv n hn0]; exact_mod_cast pow_dvd_pow 2 hn

/-! ## RingO non-vacuity: a member over the ring of integers of Q(zeta_4) meets TargetDO 2 1 1,
so thmH_cyclotomic has satisfiable hypotheses (and returns 1 <= v_2(2)). -/

open NumberField in
noncomputable abbrev O4 := 𝓞 (CyclotomicField 4 ℚ)

open NumberField in
noncomputable def B2O : ArithmeticFunction O4 :=
  FrobLevel.Dir.mapHom (Int.castRingHom O4) (Bz 2)

theorem B2O_apply {n : ℕ} (hn : n ≠ 0) : B2O n = (2 : O4) ^ ω n := by
  rw [B2O, FrobLevel.Dir.mapHom_apply, Bz_apply 2 hn]; simp

theorem B2O_target : TargetDO 2 1 1 (famO ({0} : Finset ℕ) (fun _ => (1 : O4))
    (fun _ => B2O) (fun _ => 1)) := by
  have hv : ∀ n, n ≠ 0 → famO ({0} : Finset ℕ) (fun _ => (1 : O4)) (fun _ => B2O)
      (fun _ => 1) n = (2 : O4) ^ ω n := by
    intro n hn
    show ∑ i ∈ ({0} : Finset ℕ), (1 : O4) * (B2O * 1) n = _
    rw [sum_singleton, mul_one, one_mul, B2O_apply hn]
  refine ⟨fun q hq => ⟨1, ⟨1, by simp⟩, ?_⟩, fun n hn => ?_⟩
  · rw [hv q hq.ne_zero, cardDistinctFactors_apply_prime hq]; norm_num
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [hv n hn0]
    have : ((2 : ℕ) : O4) ^ (1 + 1) ∣ (2 : O4) ^ ω n := by
      push_cast; exact pow_dvd_pow 2 hn
    exact this

example : 1 ≤ ∑ z ∈ (({0} : Finset ℕ).image (fun _ => (1 : ℤ) + 1)).erase 0,
    padicValInt 2 z :=
  thmH_cyclotomic 4 2 ({0} : Finset ℕ) (fun _ => 1 + 1) (fun _ => (1 : O4)) (fun _ => B2O)
    (fun _ => 1) {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq)
    (fun _ _ => isMultiplicative_mapHom _ (Bz_mult 2))
    (fun _ _ q hq => by
      rw [B2O_apply hq.ne_zero, cardDistinctFactors_apply_prime hq]; norm_num)
    (fun _ _ m _ hm1 => by rw [one_apply_ne hm1.ne']; exact dvd_zero _) B2O_target

/-! ## RingO: UnitModP over Z is exactly "not divisible by p". -/
example (p : ℕ) [hp : Fact p.Prime] (u : ℤ) : UnitModP p u ↔ ¬ (p : ℤ) ∣ u := by
  constructor
  · rintro ⟨w, hw⟩ hu
    exact (int_prime p).not_dvd_one (by have := dvd_sub (hu.mul_right w) hw; simpa using this)
  · intro hu
    have hpr : Prime (p : ℤ) := int_prime p
    have hcop : IsCoprime (p : ℤ) u := (Prime.coprime_iff_not_dvd hpr).2 hu
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨b, ⟨-a, by linear_combination hab⟩⟩

/-! ## Summatory: hypotheses of H9_H10 satisfiable; card_primePow_eq at small x. -/
example : (primePowLe 10).card = 7 := by decide +kernel

example : ∃ a : ℤ → ℤ, ∃ C : ℤ, ∃ v : ℕ, ∃ u : ℤ, C = 2 ^ v * u ∧ ¬ (2 : ℤ) ∣ u ∧ True :=
  by
  obtain ⟨a, C, v, u, hC, hu, -⟩ := H9_H10 2 (k := 1) ({1, 2} : Finset ℤ) (by decide) ⟨1, by simp⟩
    (by decide)
  exact ⟨a, C, v, u, hC, hu, trivial⟩

/-! ## MuShift: the hypothesis of hasLevel_zeta_kempner is satisfiable (r25 construction). -/
example : FrobLevel.kempner 2 3 ≤ FrobLevel.kempner 2 3 - 1 + 1 :=
  (hasLevel_zeta_kempner 2 (FrobLevel.Dir.hasLevel_kempner 2 (fermat_int 2) _
    (by rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, FrobLevel.Dir.zetaZ_apply one_ne_zero];
        exact isUnit_one) (by norm_num))).2

end AuditV2
