import Mathlib
import Found
import Moment
import MomentZ
import Slice
import Construct

open M2L ArithmeticFunction Finset
open scoped ArithmeticFunction.omega

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- kempner sanity: S(2^2) = 4, S(2^3) = 4 (Kempner, least N with p^k | N!)
example : FrobLevel.kempner 2 2 = 4 := by
  apply le_antisymm
  · exact FrobLevel.kempner_le 2 ((FrobLevel.pow_dvd_factorial_iff 2 2 4).1 (by decide))
  · by_contra h
    have hs := (FrobLevel.pow_dvd_factorial_iff 2 2 _).2 (FrobLevel.kempner_spec 2 2)
    have : (2:ℕ)^2 ∣ Nat.factorial 3 := hs.trans (Nat.factorial_dvd_factorial (by omega))
    exact absurd this (by decide)

-- TargetD rejects f = 0 when k >= 1 (no trivial witness)
example (p v k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) : ¬ TargetD p v k 0 := by
  rintro ⟨h1, -⟩
  obtain ⟨u, hu, hd⟩ := h1 2 Nat.prime_two
  simp only [ArithmeticFunction.zero_apply, zero_sub, dvd_neg] at hd
  have hpv : (p:ℤ)^v ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [pow_add] at hd
  have := (mul_dvd_mul_iff_left hpv).1 hd
  exact hu ((dvd_pow_self (p:ℤ) (by omega)).trans this)

-- Theorem B hypothesis satisfiable inside the family: B_2 = zeta^2 * hcorr 2 meets target D (p = 2)
example : TargetD 2 1 1 (fam {2} (fun _ => 1) zpowZeta hcorr) := by
  obtain ⟨v, hv⟩ : ∃ v, TargetD 2 v 1 (fam {2} (fun _ => 1) zpowZeta hcorr) := by
    apply targetD_of_momentTarget 2
    refine ⟨1, 1, by decide, by simp [mom], fun r hr => ?_⟩
    simp only [mom, sum_singleton, one_mul]
    exact pow_dvd_pow 2 hr
  -- v is forced by prime values: check directly at v = 1 instead
  refine ⟨fun q hq => ⟨1, by decide, ?_⟩, fun n hn => ?_⟩
  · rw [fam_hcorr_apply _ _ hq.ne_zero, cardDistinctFactors_apply_prime hq]; simp [mom]
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [fam_hcorr_apply _ _ hn0]; simp only [mom, sum_singleton, one_mul]
    exact pow_dvd_pow 2 hn

-- the twisted hypothesis "infinite set P of primes" is satisfiable with primes = 1 mod N (Mathlib)
example (N : ℕ) (hN : N ≠ 0) : {q : ℕ | q.Prime ∧ q ≡ 1 [MOD N]}.Infinite :=
  Nat.infinite_setOfPred_prime_modEq_one hN

-- thmB_arith_exists is non-vacuous: its conclusion is attained on this witness
example : ∃ z ∈ ({2} : Finset ℤ), (2:ℤ) ∣ z ∧ ¬ (2:ℤ)^2 ∣ z ∧
    ¬ (2:ℤ) ∣ agg (fun _ => 1) hcorr z := by
  refine ⟨2, by simp, by decide, by decide, ?_⟩
  show ¬ (2:ℤ) ∣ (1:ℤ) * hcorr 2 1
  rw [hcorr_one]; norm_num

-- Theorem H iff is non-vacuous at the minimum (membership half of IsLeast)
example : CheapAchievable 2 2 (FrobLevel.kempner 2 2) := (Zcheap_eq 2 (by norm_num)).1
example : SignedAchievable 2 3 (FrobLevel.kempner 2 2) := by
  have := (Zsigned_eq 2 (k := 3) (by norm_num)).1
  rwa [show (3 + 1) / 2 = 2 by norm_num] at this
-- and fails one below for a concrete case: S(2^2) = 4, so Z = 3 is not cheap-achievable at k = 2
example : ¬ CheapAchievable 2 2 3 := by
  intro h
  have := (cheap_arith_iff 2 (by norm_num) 3).1 h
  have hs := (FrobLevel.pow_dvd_factorial_iff 2 2 _).2 (FrobLevel.kempner_spec 2 2)
  have : (2:ℕ)^2 ∣ Nat.factorial 3 := hs.trans (Nat.factorial_dvd_factorial this)
  exact absurd this (by decide)

-- signatures as compiled
#check @thmH_arith
#check @cheap_arith_iff
#check @construction_explicit
#print TargetD
#print CheapAchievable
#print FrobLevel.kempner
