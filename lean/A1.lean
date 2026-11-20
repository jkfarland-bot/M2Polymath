/-
Run r25 / M2, seat M2L2 (item 1): Corollary A1 of A19 (our O1, ledger R-113).

No member of the family (integer cores congruent to their degree `z` modulo `p` on an infinite set
`P` of primes, corrections divisible by `p` on squarefree `m > 1`, any integer coefficients,
several cores per degree and degree `0` allowed) gives the prime indicator modulo `p`.

Contents.
1. `fermat_int`: `p | z ^ p - z` for every integer `z` (Fermat on the integer degree; no Frobenius
   on the coefficients).
2. `corA1_I` (main, twisted, general family): if `p` does not divide `f q` for one `q` in `P`, then
   some squarefree `n` with all prime factors in `P` and `omega(n) = p` has `p` not dividing `f n`.
   `corA1_I_false`: hence `f n = 0 (mod p)` on all squarefree `n` with `omega(n) >= 2` (with prime
   factors in `P`) is impossible.
3. `TargetU p k f`: `f q = 1 (mod p^k)` at every prime `q`, `f n = 0 (mod p^k)` on squarefree `n`
   with `omega(n) >= 2`. `not_targetU_I` (twisted), `not_targetU_untwisted` (cores with value `deg i`
   at every prime), `not_targetU_fam` (round 1's family): for every `k >= 1`, no member meets
   `TargetU p k`; hence no member gives the prime indicator modulo `p^k` (or any lift of it).
4. `Bp_sub_delta`: the integrality caveat. `E(n) = (p ^ omega(n) - [n = 1]) / p` is integer-valued,
   `E(q^e) = 1` at every prime power and `p | E(n)` for `omega(n) >= 2`; so `E` meets `TargetU p 1`.
   (Its representation `(B_p - delta) / p` has the coefficient `1 / p`; termwise integrality is
   what A1 uses.)

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

section A1

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*}

/-- Fermat on an integer: `p | z ^ p - z`. -/
theorem fermat_int (z : ℤ) : (p : ℤ) ∣ z ^ p - z := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

/-- `s_p = s_1 (mod p)` for any integer weights. -/
theorem mom_p_sub_mom_one (T : Finset ℤ) (a : ℤ → ℤ) : (p : ℤ) ∣ mom T a p - mom T a 1 := by
  rw [mom, mom, ← sum_sub_distrib]
  exact dvd_sum fun z _ => by
    rw [pow_one, ← mul_sub]; exact (fermat_int p z).mul_left _

/-- **Corollary A1 (main form, general twisted family).** Cores `G i` multiplicative with
`G i (q) = deg i (mod p)` for `q` in an infinite set `P` of primes, corrections `h i = 0 (mod p)`
on squarefree `m > 1`. If `p` does not divide `f q` for some `q` in `P`, then some squarefree `n`
with `omega(n) = p` and all prime factors in `P` has `p` not dividing `f n`. -/
theorem corA1_I (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ∣ h i m)
    {q : ℕ} (hqP : q ∈ P) (hq : ¬ (p : ℤ) ∣ famI I c G h q) :
    ∃ n, Squarefree n ∧ ω n = p ∧ (∀ q', q'.Prime → q' ∣ n → q' ∈ P) ∧
      ¬ (p : ℤ) ∣ famI I c G h n := by
  have hsl : ∀ n, Squarefree n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : ℤ) ∣ famI I c G h n - mom (I.image deg) (wt I deg (aggI c h)) (ω n) :=
    fun n hn hnP => famI_slice p I deg c G h hG hn
      (fun i hi q hq hqn => hGq i hi q (hnP q hq hqn)) hh
  obtain ⟨n, hn, hnr, hnP⟩ := exists_slice P hP hPp p
  refine ⟨n, hn, hnr, hnP, fun hfn => hq ?_⟩
  have hqq := hPp q hqP
  have h1 := hsl q hqq.prime.irreducible.squarefree (fun q' hq' hq'q => by
    rw [(Nat.prime_dvd_prime_iff_eq hq' hqq).1 hq'q]; exact hqP)
  rw [cardDistinctFactors_apply_prime hqq] at h1
  have h2 := hsl n hn hnP
  rw [hnr] at h2
  have h3 := mom_p_sub_mom_one p (I.image deg) (wt I deg (aggI c h))
  -- f q = s_1 = s_p = f n = 0 (mod p)
  have := dvd_add (dvd_sub (dvd_sub hfn h2) h3) h1
  have e : famI I c G h n - (famI I c G h n - mom (I.image deg) (wt I deg (aggI c h)) p) -
      (mom (I.image deg) (wt I deg (aggI c h)) p - mom (I.image deg) (wt I deg (aggI c h)) 1) +
      (famI I c G h q - mom (I.image deg) (wt I deg (aggI c h)) 1) = famI I c G h q := by ring
  rw [e] at this
  exact this

/-- **Corollary A1 (contradiction form).** With the hypotheses of `corA1_I`, a unit value at one
prime of `P` and `f n = 0 (mod p)` on every squarefree `n` with `omega(n) >= 2` (prime factors in
`P`) cannot both hold. -/
theorem corA1_I_false (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ∣ h i m)
    (hunit : ∃ q ∈ P, ¬ (p : ℤ) ∣ famI I c G h q)
    (hcomp : ∀ n, Squarefree n → 2 ≤ ω n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : ℤ) ∣ famI I c G h n) : False := by
  obtain ⟨q, hqP, hq⟩ := hunit
  obtain ⟨n, hn, hnr, hnP, hfn⟩ := corA1_I p I deg c G h P hP hPp hG hGq hh hqP hq
  exact hfn (hcomp n hn (by rw [hnr]; exact hp.out.two_le) hnP)

/-- Target U modulo `p^k`: the prime indicator on primes and on squarefree `n` with
`omega(n) >= 2` (values at `1` and at non-squarefree `n` free). -/
def TargetU (k : ℕ) (f : ArithmeticFunction ℤ) : Prop :=
  (∀ q : ℕ, q.Prime → (p : ℤ) ^ k ∣ f q - 1) ∧
    ∀ n : ℕ, Squarefree n → 2 ≤ ω n → (p : ℤ) ^ k ∣ f n

/-- **Corollary A1 (target U, twisted general family).** For `k >= 1` no member of the family with
cores `deg i (mod p)` on an infinite prime set `P` and corrections `0 (mod p)` on squarefree
`m > 1` meets `TargetU p k`. -/
theorem not_targetU_I {k : ℕ} (hk : 1 ≤ k) (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ∣ h i m) :
    ¬ TargetU p k (famI I c G h) := by
  rintro ⟨h1, h2⟩
  have hpk : (p : ℤ) ∣ (p : ℤ) ^ k := dvd_pow_self _ (by omega)
  obtain ⟨q, hqP⟩ := hP.nonempty
  refine corA1_I_false p I deg c G h P hP hPp hG hGq hh ⟨q, hqP, fun hdq => ?_⟩
    (fun n hn hn2 _ => hpk.trans (h2 n hn hn2))
  have := dvd_sub hdq (hpk.trans (h1 q (hPp q hqP)))
  rw [sub_sub_cancel] at this
  exact (int_prime p).not_dvd_one this

/-- **Corollary A1, untwisted.** Cores with value `deg i` at every prime (for example `zeta ^ a *
moebius ^ b`), integral corrections vanishing on squarefree `m > 1`: no member meets `TargetU p k`,
`k >= 1`. -/
theorem not_targetU_untwisted {k : ℕ} (hk : 1 ≤ k) (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) :
    ¬ TargetU p k (famI I c G h) :=
  not_targetU_I p hk I deg c G h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq) hG
    (fun i hi q hq => by rw [hGq i hi q hq, sub_self]; exact dvd_zero _)
    (fun i hi m hm hm1 => by rw [hh i hi m hm hm1]; exact dvd_zero _)

/-- **Corollary A1 for round 1's family** (`fam T c zpowZeta h`, nodes `T` any finite set of
integers, `0` allowed). -/
theorem not_targetU_fam {k : ℕ} (hk : 1 ≤ k) (T : Finset ℤ) (c : ℤ → ℤ)
    (h : ℤ → ArithmeticFunction ℤ) (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0) :
    ¬ TargetU p k (fam T c zpowZeta h) := by
  rw [fam_eq_famI]
  exact not_targetU_untwisted p hk T id c zpowZeta h (fun z _ => zpowZeta_mult z)
    (fun z _ q hq => zpowZeta_prime z hq) hh

/-! ## The integrality caveat: `(B_p - delta) / p` -/

/-- `E(n) = (p ^ omega(n) - [n = 1]) / p` for `n >= 1` (`0` at `0`); integer-valued. -/
def Ediv : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else ((p : ℤ) ^ ω n - if n = 1 then 1 else 0) / p, rfl⟩

omit hp in
theorem p_mul_Ediv {n : ℕ} (hn : n ≠ 0) :
    (p : ℤ) * Ediv p n = (p : ℤ) ^ ω n - if n = 1 then 1 else 0 := by
  show (p : ℤ) * (if n = 0 then 0 else ((p : ℤ) ^ ω n - if n = 1 then 1 else 0) / p) = _
  rw [if_neg hn]
  apply Int.mul_ediv_cancel'
  by_cases h1 : n = 1
  · subst h1; simp
  · rw [if_neg h1, sub_zero]
    have : ω n ≠ 0 := fun h => h1 (by
      have := (cardDistinctFactors_eq_zero).1 h; omega)
    exact dvd_pow_self _ this

/-- **The caveat.** `E` is `1` at every prime power and divisible by `p` when `omega(n) >= 2`: it
meets `TargetU p 1` although no family member with integral coefficients does. -/
theorem Bp_sub_delta :
    (∀ q e : ℕ, q.Prime → 1 ≤ e → Ediv p (q ^ e) = 1) ∧
      (∀ n, 2 ≤ ω n → (p : ℤ) ∣ Ediv p n) ∧ TargetU p 1 (Ediv p) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpp : ∀ q e : ℕ, q.Prime → 1 ≤ e → Ediv p (q ^ e) = 1 := by
    intro q e hq he
    have hne : q ^ e ≠ 0 := pow_ne_zero _ hq.ne_zero
    have h1 : q ^ e ≠ 1 := (Nat.one_lt_pow (by omega) hq.one_lt).ne'
    have := p_mul_Ediv p hne
    rw [if_neg h1, sub_zero, cardDistinctFactors_apply_prime_pow hq (by omega), pow_one] at this
    exact (mul_eq_left₀ hp0).1 this
  have hcomp : ∀ n, 2 ≤ ω n → (p : ℤ) ∣ Ediv p n := by
    intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hn1 : n ≠ 1 := by rintro rfl; simp at hn
    have := p_mul_Ediv p hn0
    rw [if_neg hn1, sub_zero] at this
    have h2 : (p : ℤ) ^ 2 ∣ (p : ℤ) * Ediv p n := by rw [this]; exact pow_dvd_pow _ hn
    rw [pow_two] at h2
    exact (mul_dvd_mul_iff_left hp0).1 h2
  refine ⟨hpp, hcomp, fun q hq => ?_, fun n _ hn => ?_⟩
  · rw [show q = q ^ 1 from (pow_one q).symm, hpp q 1 hq le_rfl]; simp
  · rw [pow_one]; exact hcomp n hn

end A1

end M2L2
