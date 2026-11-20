/-
Run r25 / M2, seat M2L2 (item 3): the family with several cores per degree and degree-0 terms.

A family member is indexed by a finite set `I` of an arbitrary type:
`famI I c G h = sum over i in I of c i * (G i * h i)`, with a degree `deg i` in `ℤ` (possibly `0`,
possibly repeated). The aggregated weight on a degree `z` is
`wt I deg (aggI c h) z = sum over i in I with deg i = z of c i * h i 1` (zero off the degree set).

Contents.
1. `mom_wt`: moments of the aggregated weights on the degree set equal the indexed sums.
   `mom_erase_zero`: for `r >= 1` the degree `0` contributes nothing.
2. `famI_slice` (twisted, mod `N`) and `famI_slice_exact` (untwisted): Theorem A for the general family.
3. `moments_of_targetD_I`, `thmH_I` (Theorem H lower bound: `k <= sum over nonzero degrees of v_p`),
   `cheapI_lower`, `signedI_lower` (Kempner bounds with degree `0` allowed).
4. `thmB_I`, `thmB_I_exists` (Theorem B for the general family).
5. `cheapI_iff`, `signedI_iff`, `ZcheapI_eq`, `ZsignedI_eq`: the exact iff theorems for the general
   family: any index type, cores `G i` multiplicative with value `deg i` at every prime (for example
   `zeta ^ a * moebius ^ b` with `a - b = deg i`), several cores per degree, degree-0 terms,
   corrections vanishing on squarefree `m > 1`. Degrees in `{0..Z}`: achievable iff `S(p^k) <= Z`;
   degrees in `{-Z..Z}`: iff `S(p^ceil(k/2)) <= Z`.

Lean v4.33.1 with Mathlib; imports the r25 library and round 1 (Moment, MomentZ, Slice, Construct).
-/
import Mathlib
import Found
import DirBase
import DirMain
import Moment
import MomentZ
import Slice
import Construct

namespace M2L2

open Finset ArithmeticFunction M2L
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-! ## 1. Aggregation -/

section Agg

variable {ι : Type*}

/-- The general family member `sum over i in I of c i * (G i * h i)`. -/
def famI (I : Finset ι) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => ∑ i ∈ I, c i * (G i * h i) n, by simp⟩

theorem famI_apply (I : Finset ι) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) (n : ℕ) :
    famI I c G h n = ∑ i ∈ I, c i * (G i * h i) n := rfl

/-- Round 1's family is the special case `ι = ℤ`, `deg = id`. -/
theorem fam_eq_famI (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ) :
    fam T c G h = famI T c G h := rfl

/-- Per-index weight `c i * h i 1`. -/
def aggI (c : ι → ℤ) (h : ι → ArithmeticFunction ℤ) : ι → ℤ := fun i => c i * h i 1

/-- Aggregated weight on the degree `z`: the sum of `b i` over indices of degree `z`. -/
def wt (I : Finset ι) (deg : ι → ℤ) (b : ι → ℤ) (z : ℤ) : ℤ := ∑ i ∈ I with deg i = z, b i

theorem wt_of_not_mem (I : Finset ι) (deg : ι → ℤ) (b : ι → ℤ) {z : ℤ}
    (hz : z ∉ I.image deg) : wt I deg b z = 0 := by
  apply sum_eq_zero
  intro i hi
  exact absurd ((mem_filter.mp hi).2 ▸ mem_image_of_mem deg (mem_filter.mp hi).1) hz

/-- Moments of the aggregated weights on the degree set. -/
theorem mom_wt (I : Finset ι) (deg : ι → ℤ) (b : ι → ℤ) (r : ℕ) :
    mom (I.image deg) (wt I deg b) r = ∑ i ∈ I, b i * deg i ^ r := by
  rw [mom, ← Finset.sum_fiberwise_of_maps_to (t := I.image deg) (g := deg)
    (fun i hi => mem_image_of_mem deg hi)]
  apply sum_congr rfl
  intro z _
  rw [wt, Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

/-- Degree `0` does not contribute to moments `r >= 1`. -/
theorem mom_erase_zero (T : Finset ℤ) (a : ℤ → ℤ) {r : ℕ} (hr : r ≠ 0) :
    mom (T.erase 0) a r = mom T a r := by
  unfold mom
  exact Finset.sum_erase T (by rw [zero_pow hr, mul_zero])

/-- Moments over a superset where the weights vanish off the smaller set. -/
theorem mom_subset {T T' : Finset ℤ} (hT : T ⊆ T') (a : ℤ → ℤ) (ha : ∀ z ∈ T', z ∉ T → a z = 0)
    (r : ℕ) : mom T a r = mom T' a r := by
  unfold mom
  exact Finset.sum_subset hT fun z hz hzT => by rw [ha z hz hzT, zero_mul]

end Agg

/-! ## 2. The slice formula for the general family -/

section Slice

variable {ι : Type*}

/-- **Slice formula (Theorem A), general family.** Several cores may share a degree; degree `0`
is allowed. For squarefree `n` with `G i (q) = deg i (mod N)` at its prime factors and `h i = 0
(mod N)` on squarefree `m > 1`: `famI n = sum over degrees z of wt_z z ^ omega(n) (mod N)`. -/
theorem famI_slice (N : ℕ) (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → q ∣ n → (N : ℤ) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (N : ℤ) ∣ h i m) :
    (N : ℤ) ∣ famI I c G h n - mom (I.image deg) (wt I deg (aggI c h)) (ω n) := by
  rw [mom_wt]
  let φ := Int.castRingHom (ZMod N)
  have hφ : ∀ x y : ℤ, (N : ℤ) ∣ x - y ↔ φ x = φ y := fun x y => by
    rw [eq_comm]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub y x N).symm
  rw [hφ, famI_apply, map_sum, map_sum]
  apply sum_congr rfl
  intro i hi
  have h1 : φ ((G i * h i) n) =
      (FrobLevel.Dir.mapHom φ (G i) * FrobLevel.Dir.mapHom φ (h i)) n := by
    rw [← map_mul]; rfl
  have hh' : ∀ m, Squarefree m → 1 < m → FrobLevel.Dir.mapHom φ (h i) m = 0 := by
    intro m hm hm1
    rw [FrobLevel.Dir.mapHom_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 (hh i hi m hm hm1)
  have hG' : ∀ q, q.Prime → q ∣ n → FrobLevel.Dir.mapHom φ (G i) q = φ (deg i) := by
    intro q hq hqn
    rw [FrobLevel.Dir.mapHom_apply]
    exact ((hφ _ _).1 (hGq i hi q hq hqn))
  rw [map_mul, h1, mul_apply_squarefree _ _ hn hh',
    apply_squarefree_of_mult (isMultiplicative_mapHom φ (hG i hi)) hn hG',
    FrobLevel.Dir.mapHom_apply, aggI, map_mul, map_mul, map_pow]
  ring

/-- **Slice formula, general family, untwisted (exact).** -/
theorem famI_slice_exact (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → q ∣ n → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) :
    famI I c G h n = mom (I.image deg) (wt I deg (aggI c h)) (ω n) := by
  have := famI_slice 0 I deg c G h hG hn (fun i hi q hq hqn => by simp [hGq i hi q hq hqn])
    (fun i hi m hm hm1 => by simp [hh i hi m hm hm1])
  rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at this
  exact this

end Slice

/-! ## 3. Theorem H (lower bound) and Theorem B for the general family -/

section Targets

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*}

omit hp in
/-- The moment target from `TargetD` along an infinite set `P` of primes, general family. -/
theorem moments_of_targetD_I {v k : ℕ} (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c G h)) :
    (∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      (p : ℤ) ^ (v + k) ∣ mom (I.image deg) (wt I deg (aggI c h)) 1 - p ^ v * u) ∧
    ∀ r, 2 ≤ r → (p : ℤ) ^ (v + k) ∣ mom (I.image deg) (wt I deg (aggI c h)) r := by
  have hsl : ∀ n, Squarefree n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : ℤ) ^ (v + k) ∣ famI I c G h n - mom (I.image deg) (wt I deg (aggI c h)) (ω n) := by
    intro n hn hnP
    have := famI_slice (p ^ (v + k)) I deg c G h hG hn
      (fun i hi q hq hqn => by rw [natCast_pow_int]; exact hGq i hi q (hnP q hq hqn))
      (fun i hi m hm hm1 => by rw [natCast_pow_int]; exact hh i hi m hm hm1)
    rwa [natCast_pow_int] at this
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

/-- **Theorem H, lower bound, general family (with twists).** Several cores per degree, degree `0`
allowed. If `famI I c G h` meets `TargetD p v k`, then `k <= sum over the nonzero degrees z of
v_p(z)`. -/
theorem thmH_I {v k : ℕ} (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c G h)) :
    k ≤ ∑ z ∈ (I.image deg).erase 0, padicValInt p z := by
  obtain ⟨⟨u, hu, h1⟩, hr⟩ := moments_of_targetD_I p I deg c G h P hP hPp hG hGq hh hf
  refine thmH_moment p _ (Finset.notMem_erase 0 _) (wt I deg (aggI c h)) v k u hu ?_
    (fun r hr2 _ => ?_)
  · rwa [mom_erase_zero _ _ one_ne_zero]
  · rw [mom_erase_zero _ _ (by omega)]; exact hr r hr2

/-- Untwisted general lower bound: cores with value `deg i` at every prime, exact corrections. -/
theorem thmH_I_untwisted {v k : ℕ} (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0)
    (hf : TargetD p v k (famI I c G h)) :
    k ≤ ∑ z ∈ (I.image deg).erase 0, padicValInt p z :=
  thmH_I p I deg c G h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq) hG
    (fun i hi q hq => by rw [hGq i hi q hq, sub_self]; exact dvd_zero _)
    (fun i hi m hm hm1 => by rw [hh i hi m hm hm1]; exact dvd_zero _) hf

theorem erase_subset_cheap {I : Finset ι} {deg : ι → ℤ} {Z : ℕ}
    (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ Z) : (I.image deg).erase 0 ⊆ cheapNodes Z := by
  intro z hz
  obtain ⟨hz0, hz⟩ := mem_erase.mp hz
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  have := hd i hi
  simp only [cheapNodes, mem_Icc]; omega

theorem erase_subset_signed {I : Finset ι} {deg : ι → ℤ} {Z : ℕ}
    (hd : ∀ i ∈ I, -(Z : ℤ) ≤ deg i ∧ deg i ≤ Z) : (I.image deg).erase 0 ⊆ signedNodes Z := by
  intro z hz
  obtain ⟨hz0, hz⟩ := mem_erase.mp hz
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  have := hd i hi
  simp only [signedNodes, mem_union, mem_Icc]; omega

/-- **Cheap lower bound, general family.** Degrees in `{0..Z}` (several cores per degree, degree `0`
allowed, twists by congruence on an infinite prime set): `TargetD p v k` forces `S(p^k) <= Z`. -/
theorem cheapI_lower {v k Z : ℕ} (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ Z)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c G h)) : FrobLevel.kempner p k ≤ Z := by
  have h1 := thmH_I p I deg c G h P hP hPp hG hGq hh hf
  have h2 := sum_le_sum_of_subset (f := fun z => padicValInt p z) (erase_subset_cheap hd)
  rw [sum_val_cheap] at h2
  exact FrobLevel.kempner_le p (h1.trans h2)

/-- **Signed lower bound, general family.** Degrees in `{-Z..Z}`: `S(p^ceil(k/2)) <= Z`. -/
theorem signedI_lower {v k Z : ℕ} (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ)
    (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hd : ∀ i ∈ I, -(Z : ℤ) ≤ deg i ∧ deg i ≤ Z)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ (v + k) ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h i m)
    (hf : TargetD p v k (famI I c G h)) : FrobLevel.kempner p ((k + 1) / 2) ≤ Z := by
  have h1 := thmH_I p I deg c G h P hP hPp hG hGq hh hf
  have h2 := sum_le_sum_of_subset (f := fun z => padicValInt p z) (erase_subset_signed hd)
  rw [sum_val_signed] at h2
  exact FrobLevel.kempner_le p (by omega)

/-- **Theorem B, general family (exact form).** Under target D (`TargetD p 1 1`), for every prime
`q` in `P` and `u` with `f q = p u (mod p^2)`: the sum over degrees `z` with `v_p(z) = 1` of the
aggregated weight times `z / p` is `u (mod p)`. -/
theorem thmB_I (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m)
    (hf : TargetD p 1 1 (famI I c G h)) {q : ℕ} (hqP : q ∈ P) {u : ℤ}
    (hu : (p : ℤ) ^ 2 ∣ famI I c G h q - p * u) :
    (p : ℤ) ∣ ∑ z ∈ val1 p (I.image deg), wt I deg (aggI c h) z * (z / p) - u := by
  have hq := hPp q hqP
  have hs := famI_slice (p ^ 2) I deg c G h hG hq.prime.irreducible.squarefree
    (fun i hi q' hq' hq'q => by
      push_cast; exact hGq i hi q' ((Nat.prime_dvd_prime_iff_eq hq' hq).1 hq'q ▸ hqP))
    (fun i hi m hm hm1 => by push_cast; exact hh i hi m hm hm1)
  push_cast at hs
  rw [cardDistinctFactors_apply_prime hq] at hs
  have h1 : (p : ℤ) ^ 2 ∣ mom (I.image deg) (wt I deg (aggI c h)) 1 - p * u := by
    have := dvd_sub hu hs
    rwa [sub_sub_sub_cancel_left] at this
  have h2 := hp.out.two_le
  have hr1 : 1 ≤ p * (p - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨_, hr⟩ := moments_of_targetD_I p I deg c G h P hP hPp hG hGq hh hf
  exact thmB_moment p _ _ u (r := 1 + p * (p - 1)) (by omega) (by simp) h1 (hr _ (by omega))

/-- **Theorem B, general family (existence).** Under target D some degree `z` with `v_p(z) = 1`
has aggregated weight prime to `p`. -/
theorem thmB_I_exists (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m)
    (hf : TargetD p 1 1 (famI I c G h)) :
    ∃ z ∈ I.image deg, (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧ ¬ (p : ℤ) ∣ wt I deg (aggI c h) z := by
  obtain ⟨q, hqP⟩ := hP.nonempty
  obtain ⟨u, hu, hfu⟩ := hf.1 q (hPp q hqP)
  have hfu' : (p : ℤ) ^ 2 ∣ famI I c G h q - p * u := by simpa using hfu
  have key := thmB_I p I deg c G h P hP hPp hG hGq hh hf hqP hfu'
  by_contra hne
  push Not at hne
  have hall : (p : ℤ) ∣ ∑ z ∈ val1 p (I.image deg), wt I deg (aggI c h) z * (z / p) :=
    dvd_sum fun z hz => by
      have hz' := mem_filter.mp hz
      exact (hne z hz'.1 hz'.2.1 hz'.2.2).mul_right _
  exact hu (by have := dvd_sub hall key; rwa [sub_sub_cancel] at this)

end Targets

/-! ## 4. The exact iff theorems for the general family -/

section Exact

variable (p : ℕ) [hp : Fact p.Prime]

/-- The general cheap family meets `TargetD p v k` for some `v`: any index type, degrees in
`{0..Z}` (repetition and `0` allowed), cores multiplicative with value `deg i` at every prime,
integral corrections vanishing on squarefree `m > 1`. -/
def CheapAchI (k Z : ℕ) : Prop :=
  ∃ (ι : Type) (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ),
    (∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ Z) ∧
    (∀ i ∈ I, (G i).IsMultiplicative ∧ ∀ q, q.Prime → G i q = deg i) ∧
    (∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) ∧
    ∃ v, TargetD p v k (famI I c G h)

/-- The general signed family: as `CheapAchI` with degrees in `{-Z..Z}`. -/
def SignedAchI (k Z : ℕ) : Prop :=
  ∃ (ι : Type) (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ),
    (∀ i ∈ I, -(Z : ℤ) ≤ deg i ∧ deg i ≤ Z) ∧
    (∀ i ∈ I, (G i).IsMultiplicative ∧ ∀ q, q.Prime → G i q = deg i) ∧
    (∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) ∧
    ∃ v, TargetD p v k (famI I c G h)

/-- **Theorem H, cheap, general family (exact).** For `k >= 1`: `CheapAchI p k Z` iff
`S(p^k) <= Z`. -/
theorem cheapI_iff {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) : CheapAchI p k Z ↔ FrobLevel.kempner p k ≤ Z := by
  constructor
  · rintro ⟨ι, I, deg, c, G, h, hd, hG, hh, v, hf⟩
    exact cheapI_lower p I deg c G h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq) hd
      (fun i hi => (hG i hi).1)
      (fun i hi q hq => by rw [(hG i hi).2 q hq, sub_self]; exact dvd_zero _)
      (fun i hi m hm hm1 => by rw [hh i hi m hm hm1]; exact dvd_zero _) hf
  · intro hZ
    obtain ⟨T, hT, c, h, hh, v, hf⟩ := (cheap_arith_iff p hk Z).2 hZ
    refine ⟨ℤ, T, id, c, zpowZeta, h, fun z hz => ?_, fun z _ => ⟨zpowZeta_mult z,
      fun q hq => zpowZeta_prime z hq⟩, hh, v, hf⟩
    have := hT hz
    simp only [cheapNodes, mem_Icc] at this
    exact ⟨by simp; omega, by simpa using this.2⟩

/-- **Theorem H, signed, general family (exact).** For `k >= 1`: `SignedAchI p k Z` iff
`S(p^ceil(k/2)) <= Z`. -/
theorem signedI_iff {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    SignedAchI p k Z ↔ FrobLevel.kempner p ((k + 1) / 2) ≤ Z := by
  constructor
  · rintro ⟨ι, I, deg, c, G, h, hd, hG, hh, v, hf⟩
    exact signedI_lower p I deg c G h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq)
      hd (fun i hi => (hG i hi).1)
      (fun i hi q hq => by rw [(hG i hi).2 q hq, sub_self]; exact dvd_zero _)
      (fun i hi m hm hm1 => by rw [hh i hi m hm hm1]; exact dvd_zero _) hf
  · intro hZ
    obtain ⟨T, hT, c, h, hh, v, hf⟩ := (signed_arith_iff p hk Z).2 hZ
    refine ⟨ℤ, T, id, c, zpowZeta, h, fun z hz => ?_, fun z _ => ⟨zpowZeta_mult z,
      fun q hq => zpowZeta_prime z hq⟩, hh, v, hf⟩
    have := hT hz
    simp only [signedNodes, mem_union, mem_Icc] at this
    simp only [id]; omega

/-- `Z_cheap(p, k) = S(p^k)` for the general family. -/
theorem ZcheapI_eq {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchI p k Z} (FrobLevel.kempner p k) :=
  ⟨(cheapI_iff p hk _).2 le_rfl, fun _ hZ => (cheapI_iff p hk _).1 hZ⟩

/-- `Z_signed(p, k) = S(p^ceil(k/2))` for the general family. -/
theorem ZsignedI_eq {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | SignedAchI p k Z} (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨(signedI_iff p hk _).2 le_rfl, fun _ hZ => (signedI_iff p hk _).1 hZ⟩

end Exact

/-! ## 5. Non-vacuity: two cores of degree 2 and a degree-0 core -/

/-- Witness data: index `0`: `zeta ^ 2` (degree 2), index `1`: `zeta ^ 3 * moebius` (degree 2 again),
index `2`: the unit `1` (degree 0); coefficients `1, 2, 7`; corrections `hcorr 2, hcorr 2, 1`. -/
noncomputable def exG (i : ℕ) : ArithmeticFunction ℤ :=
  if i = 0 then (ζ : ArithmeticFunction ℤ) ^ 2
  else if i = 1 then (ζ : ArithmeticFunction ℤ) ^ 3 * (μ : ArithmeticFunction ℤ) else 1

noncomputable def exH (i : ℕ) : ArithmeticFunction ℤ := if i = 2 then 1 else hcorr 2

def exC (i : ℕ) : ℤ := if i = 0 then 1 else if i = 1 then 2 else 7

theorem exG0 : exG 0 = (ζ : ArithmeticFunction ℤ) ^ 2 := by simp [exG]
theorem exG1 : exG 1 = (ζ : ArithmeticFunction ℤ) ^ 3 * (μ : ArithmeticFunction ℤ) := by simp [exG]
theorem exG2 : exG 2 = 1 := by simp [exG]
theorem exH0 : exH 0 = hcorr 2 := by simp [exH]
theorem exH1 : exH 1 = hcorr 2 := by simp [exH]
theorem exH2 : exH 2 = 1 := by simp [exH]

theorem ex_val {n : ℕ} (hn : 1 < n) : famI (Finset.range 3) exC exG exH n = 3 * 2 ^ ω n := by
  have e3 : (ζ : ArithmeticFunction ℤ) ^ 3 * (μ : ArithmeticFunction ℤ) = zpowZeta 2 := by
    rw [zpowZeta_of_pos (by norm_num), show (2 : ℤ).toNat = 2 from rfl, pow_succ, mul_assoc,
      coe_zeta_mul_moebius, mul_one]
  have e2 : (ζ : ArithmeticFunction ℤ) ^ 2 = zpowZeta 2 := by
    rw [zpowZeta_of_pos (by norm_num)]; rfl
  have hn0 : n ≠ 0 := by omega
  rw [famI_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [exG0, exG1, exG2, exH0, exH1, exH2, e2, e3, core_mul_hcorr, Bz_apply 2 hn0, one_mul,
    ArithmeticFunction.one_apply_ne (by omega), show exC 0 = 1 from rfl, show exC 1 = 2 from rfl]
  ring

/-- The witness meets target D at `p = 2` (several cores per degree and a degree-0 term). -/
theorem ex_targetD : TargetD 2 1 1 (famI (Finset.range 3) exC exG exH) := by
  refine ⟨fun q hq => ⟨1, by decide, ?_⟩, fun n hn => ?_⟩
  · rw [ex_val hq.one_lt, cardDistinctFactors_apply_prime hq]; norm_num
  · have hn1 : 1 < n := by
      by_contra h
      interval_cases n <;> simp at hn
    rw [ex_val hn1]
    have : (2 : ℤ) ^ (1 + 1) ∣ 2 ^ ω n := pow_dvd_pow 2 hn
    exact this.mul_left 3

/-- The witness lies in the general cheap family with `Z = 2` (degrees `2, 2, 0`). -/
theorem ex_cheapAchI : CheapAchI 2 1 2 := by
  refine ⟨ℕ, Finset.range 3, fun i => if i = 2 then 0 else 2, exC, exG, exH, ?_, ?_, ?_, 1,
    ex_targetD⟩
  · intro i _; dsimp only; split_ifs <;> norm_num
  · intro i hi
    have hi3 : i < 3 := Finset.mem_range.mp hi
    interval_cases i
    · refine ⟨by rw [exG0]; exact isMultiplicative_zeta.natCast.pow, fun q hq => ?_⟩
      rw [exG0, pow_apply_prime' zeta_int_one _ hq, zeta_int_prime hq]; norm_num
    · refine ⟨by rw [exG1]; exact isMultiplicative_zeta.natCast.pow.mul isMultiplicative_moebius,
        fun q hq => ?_⟩
      rw [exG1, FrobLevel.Dir.mul_apply_prime _ _ hq, pow_apply_prime' zeta_int_one _ hq,
        zeta_int_prime hq, moebius_apply_prime hq, FrobLevel.Dir.pow_apply_one, zeta_int_one]
      simp
    · refine ⟨by rw [exG2]; exact isMultiplicative_one, fun q hq => ?_⟩
      rw [exG2]
      exact ArithmeticFunction.one_apply_ne hq.one_lt.ne'
  · intro i hi m hm hm1
    have hi3 : i < 3 := Finset.mem_range.mp hi
    interval_cases i
    · rw [exH0]; exact hcorr_squarefree 2 hm hm1
    · rw [exH1]; exact hcorr_squarefree 2 hm hm1
    · rw [exH2]; exact ArithmeticFunction.one_apply_ne hm1.ne'

end M2L2
