/-
Run r25 / M2, seat M2L2 (items 4 and 7 together): twisted cores with values in a ring `O`
(Dirichlet characters with values in `O`, for example cyclotomic integers) meet the congruence
hypothesis of RingO on primes `q = 1 (mod M)`.

Contents.
1. `ellO chi j (n) = chi(n) n ^ j` for `chi : DirichletCharacter O N`; `ellOInv = moebius . ellO`;
   multiplicative; `ellOInv_mul_ellO` (Dirichlet inverse).
2. `TwFactorO`, `coreO L`, `sdegO L`; `coreO_congr`: if every level divides `M`, then
   `coreO L (q) = sdegO L (mod M O)` at every prime `q = 1 (mod M)`.
3. `thmH_twistedO`, `thmB_twistedO`, `corA1_twistedO`: Theorems H (lower bound), B and Corollary
   A1 for twisted cores with values in `O` (`O` a characteristic-0 domain with
   `IntDvdDescends p O`); `thmH_twisted_cyclotomic`: the case `O = 𝓞 (ℚ(zeta_N'))`.

Lean v4.33.1 with Mathlib; imports the r25 library, round 1, FamGen, A1, Twist and RingO.
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
import Twist
import RingO

namespace M2L2

open Finset ArithmeticFunction M2L
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

section FactorsO

variable {O : Type*} [CommRing O] {N : ℕ}

/-- `ellO chi j (n) = chi(n) n ^ j` for `n >= 1`. -/
def ellO (χ : DirichletCharacter O N) (j : ℕ) : ArithmeticFunction O :=
  ⟨fun n => if n = 0 then 0 else χ (n : ZMod N) * (n : O) ^ j, by simp⟩

theorem ellO_apply' (χ : DirichletCharacter O N) (j n : ℕ) :
    ellO χ j n = if n = 0 then 0 else χ (n : ZMod N) * (n : O) ^ j := rfl

theorem ellO_apply (χ : DirichletCharacter O N) (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ellO χ j n = χ (n : ZMod N) * (n : O) ^ j := by rw [ellO_apply', if_neg hn]

theorem ellO_one (χ : DirichletCharacter O N) (j : ℕ) : ellO χ j 1 = 1 := by
  rw [ellO_apply χ j one_ne_zero]; simp

theorem ellO_mul_apply (χ : DirichletCharacter O N) (j a b : ℕ) :
    ellO χ j (a * b) = ellO χ j a * ellO χ j b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [ellO_apply']
  rcases eq_or_ne b 0 with rfl | hb
  · simp [ellO_apply']
  rw [ellO_apply χ j (mul_ne_zero ha hb), ellO_apply χ j ha, ellO_apply χ j hb]
  push_cast
  rw [map_mul]
  ring

theorem ellO_mult (χ : DirichletCharacter O N) (j : ℕ) : (ellO χ j).IsMultiplicative :=
  ⟨ellO_one χ j, fun {m n} _ => ellO_mul_apply χ j m n⟩

/-- The inverse factor `moebius . ellO chi j`. -/
def ellOInv (χ : DirichletCharacter O N) (j : ℕ) : ArithmeticFunction O :=
  ((μ : ArithmeticFunction ℤ) : ArithmeticFunction O).pmul (ellO χ j)

theorem ellOInv_mult (χ : DirichletCharacter O N) (j : ℕ) : (ellOInv χ j).IsMultiplicative :=
  isMultiplicative_moebius.intCast.pmul (ellO_mult χ j)

theorem ellOInv_mul_ellO (χ : DirichletCharacter O N) (j : ℕ) : ellOInv χ j * ellO χ j = 1 := by
  ext n
  rw [mul_apply]
  have key : ∀ x ∈ n.divisorsAntidiagonal, ellOInv χ j x.1 * ellO χ j x.2 =
      ellO χ j n * (((μ : ArithmeticFunction ℤ) x.1 * (ζ : ArithmeticFunction ℤ) x.2 : ℤ) : O) := by
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h2 : x.2 ≠ 0 := by
      intro h; rw [h, mul_zero] at hx'; exact hx'.2 hx'.1.symm
    rw [ellOInv, pmul_apply, intCoe_apply, natCoe_apply, zeta_apply_ne h2, ← hx'.1,
      ellO_mul_apply]
    push_cast; ring
  rw [sum_congr rfl key, ← mul_sum, ← Int.cast_sum, ← mul_apply, moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with rfl | hn
  · rw [ellO_one, one_mul, one_one, Int.cast_one, one_one]
  · rw [one_apply_ne hn, one_apply_ne hn, Int.cast_zero, mul_zero]

theorem ellO_prime_congr (χ : DirichletCharacter O N) (j : ℕ) {M q : ℕ} (hN : N ∣ M)
    (hq : q.Prime) (hq1 : q ≡ 1 [MOD M]) : (M : O) ∣ ellO χ j q - 1 := by
  rw [ellO_apply χ j hq.ne_zero]
  have hz : (q : ZMod N) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff q 1 N).2 (hq1.of_dvd hN)
    rwa [Nat.cast_one] at this
  rw [hz, map_one, one_mul]
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd).1 (hq1.pow j)
  refine ⟨-(t : O), ?_⟩
  have : ((1 ^ j : ℕ) : ℤ) - ((q ^ j : ℕ) : ℤ) = (M : ℤ) * t := ht
  have h' := congrArg (fun x : ℤ => (x : O)) this
  push_cast at h'
  linear_combination -h'

theorem ellOInv_prime (χ : DirichletCharacter O N) (j : ℕ) {q : ℕ} (hq : q.Prime) :
    ellOInv χ j q = -ellO χ j q := by
  rw [ellOInv, pmul_apply, intCoe_apply, moebius_apply_prime hq]; push_cast; ring

end FactorsO

/-- A twisted factor with values in `O`. -/
structure TwFactorO (O : Type*) [CommRing O] where
  N : ℕ
  χ : DirichletCharacter O N
  j : ℕ
  inv : Bool

namespace TwFactorO

variable {O : Type*} [CommRing O]

def af (F : TwFactorO O) : ArithmeticFunction O := if F.inv then ellOInv F.χ F.j else ellO F.χ F.j

def sgn (F : TwFactorO O) : ℤ := if F.inv then -1 else 1

theorem af_mult (F : TwFactorO O) : F.af.IsMultiplicative := by
  unfold af; split_ifs
  · exact ellOInv_mult _ _
  · exact ellO_mult _ _

theorem af_congr (F : TwFactorO O) {M q : ℕ} (hN : F.N ∣ M) (hq : q.Prime)
    (hq1 : q ≡ 1 [MOD M]) : (M : O) ∣ F.af q - (F.sgn : O) := by
  have := ellO_prime_congr F.χ F.j hN hq hq1
  unfold af sgn; split_ifs
  · rw [ellOInv_prime _ _ hq]
    have e : -ellO F.χ F.j q - ((-1 : ℤ) : O) = -(ellO F.χ F.j q - 1) := by push_cast; ring
    rw [e]; exact this.neg_right
  · simpa using this

end TwFactorO

section CoreO

variable {O : Type*} [CommRing O]

def coreO (L : List (TwFactorO O)) : ArithmeticFunction O := (L.map TwFactorO.af).prod

def sdegO (L : List (TwFactorO O)) : ℤ := (L.map TwFactorO.sgn).sum

theorem coreO_mult (L : List (TwFactorO O)) : (coreO L).IsMultiplicative := by
  induction L with
  | nil => exact isMultiplicative_one
  | cons F L ih =>
    rw [coreO, List.map_cons, List.prod_cons]
    exact F.af_mult.mul ih

/-- **Twisted cores with values in `O`.** If every level divides `M`, then at every prime
`q = 1 (mod M)`: `coreO L (q) = sdegO L (mod M O)`. -/
theorem coreO_congr (L : List (TwFactorO O)) {M q : ℕ} (hN : ∀ F ∈ L, F.N ∣ M) (hq : q.Prime)
    (hq1 : q ≡ 1 [MOD M]) : (M : O) ∣ coreO L q - (sdegO L : O) := by
  induction L with
  | nil =>
    simp [coreO, sdegO, one_apply_ne hq.one_lt.ne']
  | cons F L ih =>
    have ih' := ih (fun F' hF' => hN F' (List.mem_cons_of_mem F hF'))
    have hF := F.af_congr (hN F List.mem_cons_self) hq hq1
    rw [coreO, List.map_cons, List.prod_cons, FrobLevel.Dir.mul_apply_prime _ _ hq,
      F.af_mult.map_one, show (L.map TwFactorO.af).prod = coreO L from rfl, (coreO_mult L).map_one,
      sdegO, List.map_cons, List.sum_cons, show (L.map TwFactorO.sgn).sum = sdegO L from rfl]
    have e : 1 * coreO L q + F.af q * 1 - ((F.sgn + sdegO L : ℤ) : O) =
        (coreO L q - (sdegO L : O)) + (F.af q - (F.sgn : O)) := by push_cast; ring
    rw [e]; exact dvd_add ih' hF

def twModulusO {ι : Type*} (p m : ℕ) (I : Finset ι) (L : ι → List (TwFactorO O)) : ℕ :=
  p ^ m * ∏ i ∈ I, ((L i).map TwFactorO.N).prod

theorem twModulusO_ne_zero {ι : Type*} {p : ℕ} (hp0 : p ≠ 0) (m : ℕ) (I : Finset ι)
    (L : ι → List (TwFactorO O)) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0) :
    twModulusO p m I L ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ hp0) (prod_ne_zero_iff.mpr fun i hi => ?_)
  rw [Ne, List.prod_eq_zero_iff]
  intro h
  obtain ⟨F, hF, hF0⟩ := List.mem_map.mp h
  exact hN0 i hi F hF hF0

theorem coreO_congr_pow {ι : Type*} (p : ℕ) {I : Finset ι} {L : ι → List (TwFactorO O)} (m : ℕ) :
    ∀ i ∈ I, ∀ q ∈ primesOneMod (twModulusO p m I L),
      (p : O) ^ m ∣ coreO (L i) q - (sdegO (L i) : O) := by
  intro i hi q hq
  have hdvd : ∀ F ∈ L i, F.N ∣ twModulusO p m I L := fun F hF =>
    (List.dvd_prod (List.mem_map_of_mem hF)).trans
      ((dvd_prod_of_mem (fun i => ((L i).map TwFactorO.N).prod) hi).trans (dvd_mul_left _ _))
  have hpm : (p : O) ^ m ∣ (twModulusO p m I L : O) := by
    rw [twModulusO]; push_cast; exact dvd_mul_right _ _
  exact hpm.trans (coreO_congr (L i) hdvd hq.1 hq.2)

end CoreO

section Inst

variable {O : Type*} [CommRing O] [IsDomain O] [CharZero O] (p : ℕ) [hp : Fact p.Prime]
  {ι : Type*}

/-- **Theorem H lower bound, twisted cores with values in `O`.** -/
theorem thmH_twistedO (hD : IntDvdDescends p O) {v k : ℕ} (I : Finset ι)
    (L : ι → List (TwFactorO O)) (c : ι → O) (h : ι → ArithmeticFunction O)
    (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ^ (v + k) ∣ h i m)
    (hf : TargetDO p v k (famO I c (fun i => coreO (L i)) h)) :
    k ≤ ∑ z ∈ (I.image fun i => sdegO (L i)).erase 0, padicValInt p z :=
  thmH_O p hD I (fun i => sdegO (L i)) c (fun i => coreO (L i)) h
    (primesOneMod (twModulusO p (v + k) I L))
    (primesOneMod_infinite (twModulusO_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i _ => coreO_mult (L i)) (coreO_congr_pow p (v + k)) hh hf

/-- **Theorem B, twisted cores with values in `O`.** -/
theorem thmB_twistedO (hD : IntDvdDescends p O) (I : Finset ι) (L : ι → List (TwFactorO O))
    (c : ι → O) (h : ι → ArithmeticFunction O) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ^ 2 ∣ h i m)
    (hf : TargetDO p 1 1 (famO I c (fun i => coreO (L i)) h)) :
    ∃ z ∈ I.image (fun i => sdegO (L i)), (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧
      ¬ (p : O) ∣ wtO I (fun i => sdegO (L i)) c h z :=
  thmB_O_exists p hD I (fun i => sdegO (L i)) c (fun i => coreO (L i)) h
    (primesOneMod (twModulusO p 2 I L))
    (primesOneMod_infinite (twModulusO_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i _ => coreO_mult (L i)) (coreO_congr_pow p 2) hh hf

omit [IsDomain O] [CharZero O] in
/-- **Corollary A1, twisted cores with values in `O`.** A unit value modulo `p` at one prime
`q = 1 (mod M)` and `f n = 0 (mod p O)` on all squarefree `n` with `omega(n) >= 2` cannot both
hold (`M = twModulusO p 1 I L`). -/
theorem corA1_twistedO (hD : IntDvdDescends p O) (I : Finset ι) (L : ι → List (TwFactorO O))
    (c : ι → O) (h : ι → ArithmeticFunction O) (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : O) ∣ h i m)
    {q : ℕ} (hq : q ∈ primesOneMod (twModulusO p 1 I L))
    (hunit : UnitModP p (famO I c (fun i => coreO (L i)) h q))
    (hcomp : ∀ n, Squarefree n → 2 ≤ ω n → (p : O) ∣ famO I c (fun i => coreO (L i)) h n) :
    False :=
  corA1_O p hD I (fun i => sdegO (L i)) c (fun i => coreO (L i)) h
    (primesOneMod (twModulusO p 1 I L))
    (primesOneMod_infinite (twModulusO_ne_zero hp.out.ne_zero _ I L hN0)) (fun _ hq => hq.1)
    (fun i _ => coreO_mult (L i)) (fun i hi q hq => by simpa using coreO_congr_pow p 1 i hi q hq)
    hh hq hunit (fun n hn hn2 _ => hcomp n hn hn2)

end Inst

open NumberField in
/-- **Theorem H lower bound with characters valued in cyclotomic integers.** -/
theorem thmH_twisted_cyclotomic (N' : ℕ) [NeZero N'] (p : ℕ) [hp : Fact p.Prime] {ι : Type*}
    {v k : ℕ} (I : Finset ι) (L : ι → List (TwFactorO (𝓞 (CyclotomicField N' ℚ))))
    (c : ι → 𝓞 (CyclotomicField N' ℚ)) (h : ι → ArithmeticFunction (𝓞 (CyclotomicField N' ℚ)))
    (hN0 : ∀ i ∈ I, ∀ F ∈ L i, F.N ≠ 0)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : 𝓞 (CyclotomicField N' ℚ)) ^ (v + k) ∣ h i m)
    (hf : TargetDO p v k (famO I c (fun i => coreO (L i)) h)) :
    k ≤ ∑ z ∈ (I.image fun i => sdegO (L i)).erase 0, padicValInt p z :=
  thmH_twistedO p (intDvdDescends_ringOfIntegers _ p) I L c h hN0 hh hf

end M2L2
