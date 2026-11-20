/-
Run r25 / M2, seat M2L2 (item 4): concrete twisted cores meet the congruence hypothesis.

A twisted factor is `ell chi j (n) = chi(n) n ^ j` with `chi` a Mathlib Dirichlet character with
values in `ℤ` (`DirichletCharacter ℤ N`, for example the quadratic `ZMod.χ₄` or the trivial
character, which gives the power twist `n ^ j` of `zeta`), or its Dirichlet inverse
`ellInv chi j = moebius . ell chi j` (pointwise product). A core is a finite Dirichlet product of
such factors; its signed degree counts plain factors `+1` and inverse factors `-1`.

Contents.
1. `ell`, `ellInv`: multiplicative, `ell` completely multiplicative, `ellInv_mul_ell`:
   `ellInv chi j * ell chi j = 1`; `ell_trivial_apply`: the trivial character gives `n ^ j`.
2. `TwFactor`, `core L`, `sdeg L`; `core_mult`; `core_congr`: if every character level `N` divides
   `M`, then `core L (q) = sdeg L (mod M)` at every prime `q = 1 (mod M)` (`M` may contain `p ^ m`).
3. `primesOneMod M`: primes `q = 1 (mod M)`; infinite for `M != 0`
   (`Nat.infinite_setOfPred_prime_modEq_one`).
4. Instantiations with twisted cores: `thmH_twisted` (Theorem H lower bound), `cheap_twisted_lower`
   and `signed_twisted_lower` (Kempner bounds measured by the number of factors),
   `thmB_twisted` (Theorem B), `not_targetU_twisted` (Corollary A1); the modulus is built as
   `M = p ^ m * prod of all character levels` (`twModulus`).

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

open Finset ArithmeticFunction M2L
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-! ## 1. Twisted factors -/

section Factors

variable {N : ℕ}

/-- `ell chi j (n) = chi(n) n ^ j` for `n >= 1`. -/
def ell (χ : DirichletCharacter ℤ N) (j : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else χ (n : ZMod N) * (n : ℤ) ^ j, by simp⟩

theorem ell_apply' (χ : DirichletCharacter ℤ N) (j n : ℕ) :
    ell χ j n = if n = 0 then 0 else χ (n : ZMod N) * (n : ℤ) ^ j := rfl

theorem ell_apply (χ : DirichletCharacter ℤ N) (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ell χ j n = χ (n : ZMod N) * (n : ℤ) ^ j := by rw [ell_apply', if_neg hn]

theorem ell_one (χ : DirichletCharacter ℤ N) (j : ℕ) : ell χ j 1 = 1 := by
  rw [ell_apply χ j one_ne_zero]; simp

/-- `ell` is completely multiplicative. -/
theorem ell_mul_apply (χ : DirichletCharacter ℤ N) (j a b : ℕ) :
    ell χ j (a * b) = ell χ j a * ell χ j b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [ell_apply']
  rcases eq_or_ne b 0 with rfl | hb
  · simp [ell_apply']
  rw [ell_apply χ j (mul_ne_zero ha hb), ell_apply χ j ha, ell_apply χ j hb]
  push_cast
  rw [map_mul]
  ring

theorem ell_mult (χ : DirichletCharacter ℤ N) (j : ℕ) : (ell χ j).IsMultiplicative :=
  ⟨ell_one χ j, fun {m n} _ => ell_mul_apply χ j m n⟩

/-- The trivial character gives the power twist: `ell 1 j (n) = n ^ j`. -/
theorem ell_trivial_apply (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ell (1 : DirichletCharacter ℤ 1) j n = (n : ℤ) ^ j := by
  rw [ell_apply _ j hn, Subsingleton.elim (n : ZMod 1) 1, map_one, one_mul]

/-- The inverse factor `moebius . ell chi j`. -/
def ellInv (χ : DirichletCharacter ℤ N) (j : ℕ) : ArithmeticFunction ℤ :=
  (μ : ArithmeticFunction ℤ).pmul (ell χ j)

theorem ellInv_mult (χ : DirichletCharacter ℤ N) (j : ℕ) : (ellInv χ j).IsMultiplicative :=
  isMultiplicative_moebius.pmul (ell_mult χ j)

/-- `ellInv chi j` is the Dirichlet inverse of `ell chi j`. -/
theorem ellInv_mul_ell (χ : DirichletCharacter ℤ N) (j : ℕ) : ellInv χ j * ell χ j = 1 := by
  ext n
  rw [mul_apply]
  have key : ∀ x ∈ n.divisorsAntidiagonal, ellInv χ j x.1 * ell χ j x.2 =
      ell χ j n * ((μ : ArithmeticFunction ℤ) x.1 * (ζ : ArithmeticFunction ℤ) x.2) := by
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h2 : x.2 ≠ 0 := by
      intro h; rw [h, mul_zero] at hx'; exact hx'.2 hx'.1.symm
    rw [ellInv, pmul_apply, natCoe_apply, zeta_apply_ne h2, ← hx'.1, ell_mul_apply]
    push_cast; ring
  rw [sum_congr rfl key, ← mul_sum, ← mul_apply, moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with rfl | hn
  · rw [ell_one, one_mul]
  · rw [one_apply_ne hn, mul_zero]

theorem ell_prime_congr (χ : DirichletCharacter ℤ N) (j : ℕ) {M q : ℕ} (hN : N ∣ M)
    (hq : q.Prime) (hq1 : q ≡ 1 [MOD M]) : (M : ℤ) ∣ ell χ j q - 1 := by
  rw [ell_apply χ j hq.ne_zero]
  have hz : (q : ZMod N) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff q 1 N).2 (hq1.of_dvd hN)
    rwa [Nat.cast_one] at this
  rw [hz, map_one, one_mul]
  have := (Nat.modEq_iff_dvd).1 (hq1.pow j)
  push_cast at this
  rw [one_pow] at this
  rw [← neg_sub]; exact this.neg_right

theorem ellInv_prime (χ : DirichletCharacter ℤ N) (j : ℕ) {q : ℕ} (hq : q.Prime) :
    ellInv χ j q = -ell χ j q := by
  rw [ellInv, pmul_apply, moebius_apply_prime hq]; ring

end Factors

/-! ## 2. Cores and their congruence on primes `1 (mod M)` -/

/-- A twisted factor: a Dirichlet character with values in `ℤ` of level `N`, a power `j`, and
whether the factor is inverted. -/
structure TwFactor where
  N : ℕ
  χ : DirichletCharacter ℤ N
  j : ℕ
  inv : Bool

namespace TwFactor

/-- The factor as an arithmetic function. -/
def af (F : TwFactor) : ArithmeticFunction ℤ := if F.inv then ellInv F.χ F.j else ell F.χ F.j

/-- Its signed degree: `-1` for an inverse factor, `+1` otherwise. -/
def sgn (F : TwFactor) : ℤ := if F.inv then -1 else 1

theorem af_mult (F : TwFactor) : F.af.IsMultiplicative := by
  unfold af; split_ifs
  · exact ellInv_mult _ _
  · exact ell_mult _ _

theorem af_congr (F : TwFactor) {M q : ℕ} (hN : F.N ∣ M) (hq : q.Prime) (hq1 : q ≡ 1 [MOD M]) :
    (M : ℤ) ∣ F.af q - F.sgn := by
  have := ell_prime_congr F.χ F.j hN hq hq1
  unfold af sgn; split_ifs
  · rw [ellInv_prime _ _ hq]
    have e : -ell F.χ F.j q - -1 = -(ell F.χ F.j q - 1) := by ring
    rw [e]; exact this.neg_right
  · exact this

end TwFactor

/-- The core: the Dirichlet product of the factors. -/
def core (L : List TwFactor) : ArithmeticFunction ℤ := (L.map TwFactor.af).prod

/-- The signed degree of a core. -/
def sdeg (L : List TwFactor) : ℤ := (L.map TwFactor.sgn).sum

theorem core_mult (L : List TwFactor) : (core L).IsMultiplicative := by
  induction L with
  | nil => exact isMultiplicative_one
  | cons F L ih =>
    rw [core, List.map_cons, List.prod_cons]
    exact F.af_mult.mul ih

/-- **Twisted cores satisfy the congruence hypothesis.** If every character level divides `M`,
then at every prime `q = 1 (mod M)`: `core L (q) = sdeg L (mod M)`. -/
theorem core_congr (L : List TwFactor) {M q : ℕ} (hN : ∀ F ∈ L, F.N ∣ M) (hq : q.Prime)
    (hq1 : q ≡ 1 [MOD M]) : (M : ℤ) ∣ core L q - sdeg L := by
  induction L with
  | nil =>
    simp [core, sdeg, one_apply_ne hq.one_lt.ne']
  | cons F L ih =>
    have ih' := ih (fun F' hF' => hN F' (List.mem_cons_of_mem F hF'))
    have hF := F.af_congr (hN F List.mem_cons_self) hq hq1
    rw [core, List.map_cons, List.prod_cons, FrobLevel.Dir.mul_apply_prime _ _ hq,
      F.af_mult.map_one, show (L.map TwFactor.af).prod = core L from rfl, (core_mult L).map_one,
      sdeg, List.map_cons, List.sum_cons, show (L.map TwFactor.sgn).sum = sdeg L from rfl]
    have e : 1 * core L q + F.af q * 1 - (F.sgn + sdeg L) =
        (core L q - sdeg L) + (F.af q - F.sgn) := by ring
    rw [e]; exact dvd_add ih' hF

theorem sdeg_le_length (L : List TwFactor) : |sdeg L| ≤ L.length := by
  induction L with
  | nil => simp [sdeg]
  | cons F L ih =>
    rw [sdeg, List.map_cons, List.sum_cons, show (L.map TwFactor.sgn).sum = sdeg L from rfl,
      List.length_cons]
    have : |F.sgn| = 1 := by unfold TwFactor.sgn; split_ifs <;> simp
    push_cast
    calc |F.sgn + sdeg L| ≤ |F.sgn| + |sdeg L| := abs_add_le _ _
      _ ≤ _ := by rw [this]; linarith

theorem sdeg_of_plain (L : List TwFactor) (hL : ∀ F ∈ L, F.inv = false) :
    sdeg L = L.length := by
  induction L with
  | nil => simp [sdeg]
  | cons F L ih =>
    rw [sdeg, List.map_cons, List.sum_cons, show (L.map TwFactor.sgn).sum = sdeg L from rfl,
      ih (fun F' hF' => hL F' (List.mem_cons_of_mem F hF')), List.length_cons]
    have : F.sgn = 1 := by unfold TwFactor.sgn; rw [hL F List.mem_cons_self]; rfl
    rw [this]; push_cast; ring

/-! ## 3. The prime set -/

/-- Primes `q = 1 (mod M)`. -/
def primesOneMod (M : ℕ) : Set ℕ := {q | q.Prime ∧ q ≡ 1 [MOD M]}

theorem primesOneMod_infinite {M : ℕ} (hM : M ≠ 0) : (primesOneMod M).Infinite :=
  Nat.infinite_setOfPred_prime_modEq_one hM

/-- The modulus `p ^ m * prod over i in I, over factors F of L i, of F.N`. -/
def twModulus {ι : Type*} (p m : ℕ) (I : Finset ι) (L : ι → List TwFactor) : ℕ :=
  p ^ m * ∏ i ∈ I, ((L i).map TwFactor.N).prod

theorem twModulus_ne_zero {ι : Type*} {p : ℕ} (hp0 : p ≠ 0) (m : ℕ) (I : Finset ι)
    (L : ι → List TwFactor) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0) : twModulus p m I L ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ hp0) (prod_ne_zero_iff.mpr fun i hi => ?_)
  rw [Ne, List.prod_eq_zero_iff]
  intro h
  obtain ⟨F, hF, hF0⟩ := List.mem_map.mp h
  exact hN0 i hi F hF hF0

theorem dvd_twModulus {ι : Type*} (p m : ℕ) (I : Finset ι) (L : ι → List TwFactor) {i : ι}
    (hi : i ∈ I) {F : TwFactor} (hF : F ∈ L i) : F.N ∣ twModulus p m I L :=
  (List.dvd_prod (List.mem_map_of_mem hF)).trans
    ((dvd_prod_of_mem (fun i => ((L i).map TwFactor.N).prod) hi).trans (dvd_mul_left _ _))

theorem pow_dvd_twModulus {ι : Type*} (p m : ℕ) (I : Finset ι) (L : ι → List TwFactor) :
    (p : ℤ) ^ m ∣ (twModulus p m I L : ℤ) := by
  rw [twModulus]; push_cast; exact dvd_mul_right _ _

/-! ## 4. Instantiations -/

section Inst

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*}

omit hp in
theorem core_congr_pow {I : Finset ι} {L : ι → List TwFactor} (m : ℕ) :
    ∀ i ∈ I, ∀ q ∈ primesOneMod (twModulus p m I L), (p : ℤ) ^ m ∣ core (L i) q - sdeg (L i) :=
  fun i hi _ hq => (pow_dvd_twModulus p m I L).trans
    (core_congr (L i) (fun _ hF => dvd_twModulus p m I L hi hF) hq.1 hq.2)

/-- **Theorem H lower bound with twisted cores.** Cores are products of factors `chi(n) n ^ j` and
their inverses (characters of nonzero levels with values in `ℤ`); corrections `0 (mod p^(v+k))`
on squarefree `m > 1`. If the member meets `TargetD p v k`, then `k <= sum over the nonzero
signed degrees z of v_p(z)`. -/
theorem thmH_twisted {v k : ℕ} (I : Finset ι) (L : ι → List TwFactor) (c : ι → ℤ)
    (h : ι → ArithmeticFunction ℤ) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c (fun i => core (L i)) h)) :
    k ≤ ∑ z ∈ (I.image fun i => sdeg (L i)).erase 0, padicValInt p z :=
  thmH_I p I (fun i => sdeg (L i)) c (fun i => core (L i)) h (primesOneMod (twModulus p (v + k) I L))
    (primesOneMod_infinite (twModulus_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i _ => core_mult (L i)) (core_congr_pow p (v + k)) hh hf

/-- **Cheap bound with twisted cores.** No inverse factors and at most `Z` factors per core:
`S(p^k) <= Z`. -/
theorem cheap_twisted_lower {v k Z : ℕ} (I : Finset ι) (L : ι → List TwFactor) (c : ι → ℤ)
    (h : ι → ArithmeticFunction ℤ) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hplain : ∀ i ∈ I, ∀ F ∈ L i, F.inv = false) (hlen : ∀ i ∈ I, (L i).length ≤ Z)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c (fun i => core (L i)) h)) : FrobLevel.kempner p k ≤ Z :=
  cheapI_lower p I (fun i => sdeg (L i)) c (fun i => core (L i)) h
    (primesOneMod (twModulus p (v + k) I L))
    (primesOneMod_infinite (twModulus_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i hi => by
      rw [sdeg_of_plain _ (hplain i hi)]; exact ⟨by positivity, by exact_mod_cast hlen i hi⟩)
    (fun i _ => core_mult (L i)) (core_congr_pow p (v + k)) hh hf

/-- **Signed bound with twisted cores.** At most `Z` factors per core (plain or inverse):
`S(p^ceil(k/2)) <= Z`. -/
theorem signed_twisted_lower {v k Z : ℕ} (I : Finset ι) (L : ι → List TwFactor) (c : ι → ℤ)
    (h : ι → ArithmeticFunction ℤ) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hlen : ∀ i ∈ I, (L i).length ≤ Z)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c (fun i => core (L i)) h)) :
    FrobLevel.kempner p ((k + 1) / 2) ≤ Z :=
  signedI_lower p I (fun i => sdeg (L i)) c (fun i => core (L i)) h
    (primesOneMod (twModulus p (v + k) I L))
    (primesOneMod_infinite (twModulus_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i hi => by
      have h1 := sdeg_le_length (L i)
      have h2 : ((L i).length : ℤ) ≤ Z := by exact_mod_cast hlen i hi
      exact ⟨by linarith [neg_abs_le (sdeg (L i))], by linarith [le_abs_self (sdeg (L i))]⟩)
    (fun i _ => core_mult (L i)) (core_congr_pow p (v + k)) hh hf

/-- **Theorem B with twisted cores.** Under target D some signed degree `z` with `v_p(z) = 1` has
aggregated weight prime to `p`. -/
theorem thmB_twisted (I : Finset ι) (L : ι → List TwFactor) (c : ι → ℤ)
    (h : ι → ArithmeticFunction ℤ) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m)
    (hf : TargetD p 1 1 (famI I c (fun i => core (L i)) h)) :
    ∃ z ∈ I.image (fun i => sdeg (L i)), (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧
      ¬ (p : ℤ) ∣ wt I (fun i => sdeg (L i)) (aggI c h) z :=
  thmB_I_exists p I (fun i => sdeg (L i)) c (fun i => core (L i)) h
    (primesOneMod (twModulus p 2 I L))
    (primesOneMod_infinite (twModulus_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i _ => core_mult (L i)) (core_congr_pow p 2) hh hf

/-- **Corollary A1 with twisted cores.** No member gives the prime indicator modulo `p^k`,
`k >= 1`. -/
theorem not_targetU_twisted {k : ℕ} (hk : 1 ≤ k) (I : Finset ι) (L : ι → List TwFactor)
    (c : ι → ℤ) (h : ι → ArithmeticFunction ℤ) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ∣ h i m) :
    ¬ TargetU p k (famI I c (fun i => core (L i)) h) :=
  not_targetU_I p hk I (fun i => sdeg (L i)) c (fun i => core (L i)) h
    (primesOneMod (twModulus p 1 I L))
    (primesOneMod_infinite (twModulus_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i _ => core_mult (L i))
    (fun i hi q hq => by simpa using core_congr_pow p 1 i hi q hq) hh

end Inst

/-! ## 5. Concrete twists -/

/-- The quadratic character mod 4 (`ZMod.χ₄`, values in `ℤ`) as a factor of degree `+1`. -/
def chi4F (j : ℕ) (inv : Bool) : TwFactor := ⟨4, ZMod.χ₄, j, inv⟩

/-- The power twist `n ^ j` of `zeta` (trivial character of level 1) as a factor. -/
noncomputable def powF (j : ℕ) (inv : Bool) : TwFactor := ⟨1, 1, j, inv⟩

theorem powF_apply (j : ℕ) {n : ℕ} (hn : n ≠ 0) : (powF j false).af n = (n : ℤ) ^ j := by
  simp only [TwFactor.af, powF, Bool.false_eq_true, if_false]
  exact ell_trivial_apply j hn

theorem chi4F_apply (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (chi4F j false).af n = ZMod.χ₄ (n : ZMod 4) * (n : ℤ) ^ j := by
  simp only [TwFactor.af, chi4F, Bool.false_eq_true, if_false]
  exact ell_apply _ j hn

/-- Example: the core `L(s - 1, chi_4) * zeta(s - 2) * zeta(s)^(-1)` (factors `chi_4(n) n`,
`n ^ 2`, and `moebius`), signed degree `1`, is `1 (mod 4 * 3 ^ 5)` at every prime
`q = 1 (mod 4 * 3 ^ 5)`. -/
example {q : ℕ} (hq : q.Prime) (hq1 : q ≡ 1 [MOD 4 * 3 ^ 5]) :
    ((4 * 3 ^ 5 : ℕ) : ℤ) ∣ core [chi4F 1 false, powF 2 false, powF 0 true] q - 1 := by
  have := core_congr [chi4F 1 false, powF 2 false, powF 0 true] (M := 4 * 3 ^ 5)
    (fun F hF => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hF
      rcases hF with rfl | rfl | rfl <;> simp [chi4F, powF]) hq hq1
  have e : sdeg [chi4F 1 false, powF 2 false, powF 0 true] = 1 := by
    simp [sdeg, TwFactor.sgn, chi4F, powF]
  rwa [e] at this

/-- Example instantiation of Theorem H at `p = 3` with twisted cores of the above shape
(the hypotheses of `thmH_twisted` are met by any coefficients and corrections). -/
example {ι : Type*} (I : Finset ι) (L : ι → List TwFactor) (c : ι → ℤ)
    (h : ι → ArithmeticFunction ℤ)
    (hL : ∀ i ∈ I, ∀ F ∈ L i, F = chi4F 1 false ∨ F = powF 2 false ∨ F = powF 0 true)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) {v k : ℕ}
    (hf : TargetD 3 v k (famI I c (fun i => core (L i)) h)) :
    k ≤ ∑ z ∈ (I.image fun i => sdeg (L i)).erase 0, padicValInt 3 z :=
  thmH_twisted 3 I L c h
    (fun i hi F hF => by rcases hL i hi F hF with rfl | rfl | rfl <;> simp [chi4F, powF])
    (fun i hi m hm hm1 => by rw [hh i hi m hm hm1]; exact dvd_zero _) hf

end M2L2
