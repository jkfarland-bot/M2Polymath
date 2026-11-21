module

public import Mathlib
public import Construct
public import RingO
public import Twist
public import M2FilterD

/-!
  Seat M2L4, item 3: Theorem H as an exact iff / IsLeast over a ring O (every characteristic-zero
  domain with p^m O ∩ Z = p^m Z, in particular every ring of integers and O = Z[zeta_N]), and a
  TargetD member built from the nontrivial character chi_4 attaining the twisted lower bound.
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace M2L4
open M2L M2L2

/-! ## Transfer of the integer target to `O` -/

section Transfer

variable {O : Type*} [CommRing O]

lemma unitModP_of_not_dvd (p : ℕ) [hp : Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    UnitModP p (u : O) := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpr).2 hu
  refine ⟨(b : O), ⟨-(a : O), ?_⟩⟩
  have := congrArg (fun t : ℤ => (t : O)) hab
  push_cast at this
  linear_combination this

lemma intCast_dvd_intCast {a b : ℤ} (h : a ∣ b) : (a : O) ∣ (b : O) := by
  obtain ⟨c, rfl⟩ := h; exact ⟨c, by push_cast; ring⟩

/-- An integer member meeting `TargetD` meets `TargetDO` after the cast to `O`. -/
theorem targetDO_of_targetD [IsDomain O] [CharZero O] (p : ℕ) [hp : Fact p.Prime] {v k : ℕ} {f : ArithmeticFunction ℤ}
    (hf : TargetD p v k f) : TargetDO (O := O) p v k (f : ArithmeticFunction O) := by
  refine ⟨fun q hq => ?_, fun n hn => ?_⟩
  · obtain ⟨u, hu, hdiv⟩ := hf.1 q hq
    refine ⟨(u : O), unitModP_of_not_dvd p hu, ?_⟩
    have := intCast_dvd_intCast (O := O) hdiv
    rw [intCoe_apply]; push_cast at this; exact this
  · have := intCast_dvd_intCast (O := O) (hf.2 n hn)
    rw [intCoe_apply]; push_cast at this; exact this

/-- The round 1 family, cast to `O`, is a `famO` member with cast cores, weights and corrections. -/
theorem famO_cast (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ) :
    famO T (fun z => (c z : O)) (fun z => (G z : ArithmeticFunction O))
        (fun z => (h z : ArithmeticFunction O))
      = ((fam T c G h : ArithmeticFunction ℤ) : ArithmeticFunction O) := by
  ext n
  rw [intCoe_apply, fam_apply]
  simp only [famO, coe_mk, ← intCoe_mul, intCoe_apply]
  push_cast
  rfl

end Transfer

/-! ## The exact node bounds over `O` -/

section ExactO

variable (O : Type*) [CommRing O] [IsDomain O] [CharZero O]

/-- Over `O`: some member with cores `G i` multiplicative and equal to an integer degree
`deg i ∈ {1..Z}` at every prime (e.g. `zeta ^ deg i`), coefficients in `O`, corrections in `O`
vanishing on squarefree `m > 1`, meets `TargetDO p v k` for some `v`. -/
def CheapAchievableO (p k Z : ℕ) : Prop :=
  ∃ I : Finset ℤ, ∃ deg : ℤ → ℤ, ∃ c : ℤ → O, ∃ G h : ℤ → ArithmeticFunction O,
    (∀ i ∈ I, deg i ∈ cheapNodes Z) ∧
    (∀ i ∈ I, (G i).IsMultiplicative ∧ ∀ q, q.Prime → G i q = deg i) ∧
    (∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) ∧
    ∃ v, TargetDO p v k (famO I c G h)

/-- The same with signed degrees in `{-Z..-1} ∪ {1..Z}` (e.g. `zeta ^ z` and `moebius ^ |z|`). -/
def SignedAchievableO (p k Z : ℕ) : Prop :=
  ∃ I : Finset ℤ, ∃ deg : ℤ → ℤ, ∃ c : ℤ → O, ∃ G h : ℤ → ArithmeticFunction O,
    (∀ i ∈ I, deg i ∈ signedNodes Z) ∧
    (∀ i ∈ I, (G i).IsMultiplicative ∧ ∀ q, q.Prime → G i q = deg i) ∧
    (∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) ∧
    ∃ v, TargetDO p v k (famO I c G h)

variable (p : ℕ) [hp : Fact p.Prime]

lemma lowerO_sum {k : ℕ} (hD : IntDvdDescends p O) {I : Finset ℤ} {deg : ℤ → ℤ} {c : ℤ → O}
    {G h : ℤ → ArithmeticFunction O}
    (hG : ∀ i ∈ I, (G i).IsMultiplicative ∧ ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) {v : ℕ}
    (hf : TargetDO p v k (famO I c G h)) :
    k ≤ ∑ z ∈ (I.image deg).erase 0, padicValInt p z :=
  thmH_O p hD I deg c G h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq)
    (fun i hi => (hG i hi).1)
    (fun i hi q hq => by rw [(hG i hi).2 q hq, sub_self]; exact dvd_zero _)
    (fun i hi m hm hm1 => by rw [hh i hi m hm hm1]; exact dvd_zero _) hf

/-- **Theorem H, cheap, exact over `O`.** For `k ≥ 1`: `CheapAchievableO O p k Z ↔ S(p^k) ≤ Z`. -/
theorem cheapO_iff (hD : IntDvdDescends p O) {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    CheapAchievableO O p k Z ↔ FrobLevel.kempner p k ≤ Z := by
  constructor
  · rintro ⟨I, deg, c, G, h, hdeg, hG, hh, v, hf⟩
    have h1 := lowerO_sum O p hD hG hh hf
    have hsub : (I.image deg).erase 0 ⊆ cheapNodes Z := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.1 (mem_of_mem_erase hz)
      exact hdeg i hi
    have h2 := sum_le_sum_of_subset (f := fun z => padicValInt p z) hsub
    rw [sum_val_cheap] at h2
    exact FrobLevel.kempner_le p (h1.trans h2)
  · intro hZ
    obtain ⟨T, hT, c, h, hh, v, hf⟩ := (cheap_arith_iff p hk Z).2 hZ
    refine ⟨T, id, fun z => (c z : O), fun z => (zpowZeta z : ArithmeticFunction O),
      fun z => (h z : ArithmeticFunction O), fun i hi => hT hi, fun i _ => ⟨(zpowZeta_mult i).intCast,
      fun q hq => by rw [intCoe_apply, zpowZeta_prime i hq]; rfl⟩,
      fun i hi m hm hm1 => by rw [intCoe_apply, hh i hi m hm hm1, Int.cast_zero], v, ?_⟩
    rw [famO_cast]
    exact targetDO_of_targetD p hf

/-- **Theorem H, signed, exact over `O`.** For `k ≥ 1`:
`SignedAchievableO O p k Z ↔ S(p^⌈k/2⌉) ≤ Z`. -/
theorem signedO_iff (hD : IntDvdDescends p O) {k : ℕ} (hk : 1 ≤ k) (Z : ℕ) :
    SignedAchievableO O p k Z ↔ FrobLevel.kempner p ((k + 1) / 2) ≤ Z := by
  constructor
  · rintro ⟨I, deg, c, G, h, hdeg, hG, hh, v, hf⟩
    have h1 := lowerO_sum O p hD hG hh hf
    have hsub : (I.image deg).erase 0 ⊆ signedNodes Z := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.1 (mem_of_mem_erase hz)
      exact hdeg i hi
    have h2 := sum_le_sum_of_subset (f := fun z => padicValInt p z) hsub
    rw [sum_val_signed] at h2
    exact FrobLevel.kempner_le p (by omega)
  · intro hZ
    obtain ⟨T, hT, c, h, hh, v, hf⟩ := (signed_arith_iff p hk Z).2 hZ
    refine ⟨T, id, fun z => (c z : O), fun z => (zpowZeta z : ArithmeticFunction O),
      fun z => (h z : ArithmeticFunction O), fun i hi => hT hi, fun i _ => ⟨(zpowZeta_mult i).intCast,
      fun q hq => by rw [intCoe_apply, zpowZeta_prime i hq]; rfl⟩,
      fun i hi m hm hm1 => by rw [intCoe_apply, hh i hi m hm hm1, Int.cast_zero], v, ?_⟩
    rw [famO_cast]
    exact targetDO_of_targetD p hf

/-- **(H2) over `O`**: `Z_cheap(p, k) = S(p^k)`. -/
theorem ZcheapO_eq (hD : IntDvdDescends p O) {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievableO O p k Z} (FrobLevel.kempner p k) :=
  ⟨(cheapO_iff O p hD hk _).2 le_rfl, fun _ hZ => (cheapO_iff O p hD hk _).1 hZ⟩

/-- **(H1) over `O`**: `Z_signed(p, k) = S(p^⌈k/2⌉)`. -/
theorem ZsignedO_eq (hD : IntDvdDescends p O) {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | SignedAchievableO O p k Z} (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨(signedO_iff O p hD hk _).2 le_rfl, fun _ hZ => (signedO_iff O p hD hk _).1 hZ⟩

end ExactO

open NumberField in
/-- **(H1), (H2) over `O = 𝓞(ℚ(ζ_N)) = ℤ[ζ_N]`**, for every `N ≥ 1`, prime `p`, `k ≥ 1`. -/
theorem Z_cyclotomic_eq (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievableO (𝓞 (CyclotomicField N ℚ)) p k Z} (FrobLevel.kempner p k) ∧
    IsLeast {Z | SignedAchievableO (𝓞 (CyclotomicField N ℚ)) p k Z}
      (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨ZcheapO_eq _ p (intDvdDescends_ringOfIntegers _ p) hk,
   ZsignedO_eq _ p (intDvdDescends_ringOfIntegers _ p) hk⟩

open NumberField in
/-- The same for every number field `K` (ring of integers `𝓞 K`). -/
theorem Z_ringOfIntegers_eq (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] {k : ℕ}
    (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievableO (𝓞 K) p k Z} (FrobLevel.kempner p k) ∧
    IsLeast {Z | SignedAchievableO (𝓞 K) p k Z} (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨ZcheapO_eq _ p (intDvdDescends_ringOfIntegers _ p) hk,
   ZsignedO_eq _ p (intDvdDescends_ringOfIntegers _ p) hk⟩

/-- `p^m ℤ_p ∩ ℤ = p^m ℤ`: the descent hypothesis for the `p`-adic integers, a coefficient ring in
which every integer prime to `p` is inverted. -/
theorem intDvdDescends_padicInt (p : ℕ) [Fact p.Prime] : IntDvdDescends p ℤ_[p] := by
  intro m x hx
  have h0 : PadicInt.toZModPow m ((x : ℤ_[p])) = 0 := by
    obtain ⟨y, hy⟩ := hx
    rw [hy, map_mul, map_pow, map_natCast]
    have : ((p : ZMod (p ^ m))) ^ m = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [this, zero_mul]
  rw [map_intCast] at h0
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd x (p ^ m)).1 h0
  exact_mod_cast this

/-- **(H1), (H2) over `ℤ_p`** (integers prime to `p` inverted in the coefficient ring). -/
theorem Z_padicInt_eq (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievableO ℤ_[p] p k Z} (FrobLevel.kempner p k) ∧
    IsLeast {Z | SignedAchievableO ℤ_[p] p k Z} (FrobLevel.kempner p ((k + 1) / 2)) :=
  ⟨ZcheapO_eq _ p (intDvdDescends_padicInt p) hk, ZsignedO_eq _ p (intDvdDescends_padicInt p) hk⟩

/-! ## A TargetD member built from the nontrivial character `χ₄` -/

section Chi4

/-- `χ₄` is nontrivial: `χ₄(3) = -1`. -/
theorem chi4_nontrivial : ZMod.χ₄ ≠ 1 := by
  intro h
  have h3 : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four (by norm_num)
  have hu : IsUnit ((3 : ℕ) : ZMod 4) := by decide
  rw [h, MulChar.one_apply hu] at h3
  norm_num at h3

/-- The core `n ↦ ∑_{d ∣ n} d χ₄(n/d)`, i.e. `L(s-1) L(s, χ₄)`: factors `n` and `χ₄(n)`,
signed degree 2. -/
noncomputable def L4 : List TwFactor := [powF 1 false, chi4F 0 false]

noncomputable def L4inv : List TwFactor := [powF 1 true, chi4F 0 true]

lemma sdeg_L4 : sdeg L4 = 2 := by simp [sdeg, L4, TwFactor.sgn, powF, chi4F]

lemma core_L4_mult : (core L4).IsMultiplicative := core_mult L4

lemma core_L4_prime {q : ℕ} (hq : q.Prime) :
    core L4 q = (q : ℤ) + ZMod.χ₄ (q : ZMod 4) := by
  have e : core L4 = (powF 1 false).af * (chi4F 0 false).af := by simp [core, L4]
  rw [e, M2L3.mul_apply_prime (TwFactor.af_mult _) (TwFactor.af_mult _) hq,
    powF_apply 1 hq.ne_zero, chi4F_apply 0 hq.ne_zero]
  ring

lemma core_L4_mul_inv : core L4 * core L4inv = 1 := by
  have e1 : core L4 = ell (1 : DirichletCharacter ℤ 1) 1 * ell ZMod.χ₄ 0 := by
    simp [core, L4, TwFactor.af, powF, chi4F]
  have e2 : core L4inv = ellInv (1 : DirichletCharacter ℤ 1) 1 * ellInv ZMod.χ₄ 0 := by
    simp [core, L4inv, TwFactor.af, powF, chi4F]
  rw [e1, e2]
  calc ell (1 : DirichletCharacter ℤ 1) 1 * ell ZMod.χ₄ 0
        * (ellInv (1 : DirichletCharacter ℤ 1) 1 * ellInv ZMod.χ₄ 0)
      = (ellInv (1 : DirichletCharacter ℤ 1) 1 * ell (1 : DirichletCharacter ℤ 1) 1)
        * (ellInv ZMod.χ₄ 0 * ell ZMod.χ₄ 0) := by ring
    _ = 1 := by rw [ellInv_mul_ell, ellInv_mul_ell, one_mul]

/-- The value at every prime: `q + χ₄(q) ≡ 2 (mod 4)` (as `χ₄(q) ≡ q (mod 4)` for odd `q`,
and `2 + χ₄(2) = 2`). -/
lemma core_L4_prime_mod4 {q : ℕ} (hq : q.Prime) : (4 : ℤ) ∣ core L4 q - 2 := by
  rw [core_L4_prime hq, ZMod.χ₄_nat_eq_if_mod_four]
  rcases hq.eq_two_or_odd with rfl | hodd
  · norm_num
  · have h4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rw [ite_eq_right (by omega)]
    rcases h4 with h | h
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right (by omega)]; omega

/-- The multiplicative function with value `q + χ₄(q)` at every prime power `q^e`, `e ≥ 1`. -/
noncomputable def B4 : ArithmeticFunction ℤ := prodPrimeFactors (fun q => core L4 q)

lemma B4_mult : B4.IsMultiplicative := IsMultiplicative.prodPrimeFactors _

/-- The correction `h = core(L4)⁻¹ * B4`. -/
noncomputable def h4 : ArithmeticFunction ℤ := core L4inv * B4

lemma core_mul_h4 : core L4 * h4 = B4 := by
  rw [h4, ← mul_assoc, core_L4_mul_inv, one_mul]

lemma h4_prime {q : ℕ} (hq : q.Prime) : h4 q = 0 := by
  have hinv : core L4inv q = -core L4 q := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f q) core_L4_mul_inv
    rw [M2L3.mul_apply_prime core_L4_mult (core_mult L4inv) hq, one_apply_ne hq.one_lt.ne'] at this
    linarith
  rw [h4, M2L3.mul_apply_prime (core_mult L4inv) B4_mult hq, hinv, B4,
    prodPrimeFactors_apply hq.ne_zero, hq.primeFactors, prod_singleton]
  ring

/-- `h4` vanishes on squarefree `m > 1`. -/
theorem h4_squarefree {m : ℕ} (hm : Squarefree m) (hm1 : 1 < m) : h4 m = 0 := by
  have hmult : h4.IsMultiplicative := (core_mult L4inv).mul B4_mult
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  obtain ⟨r, rfl⟩ := hqm
  have hcop : Nat.Coprime q r := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    rintro ⟨s, rfl⟩
    have := hm q ⟨s, by ring⟩
    exact hq.one_lt.ne' (Nat.isUnit_iff.1 this)
  rw [hmult.map_mul_of_coprime hcop, h4_prime hq, zero_mul]

/-- The member: one index, core `L4`, coefficient `1`, correction `h4`. -/
noncomputable def chi4Member : ArithmeticFunction ℤ :=
  M2L2.famI ({()} : Finset Unit) (fun _ => 1) (fun _ => core L4) (fun _ => h4)

lemma chi4Member_eq : chi4Member = B4 := by
  ext n
  simp [chi4Member, M2L2.famI_apply, core_mul_h4]

/-- **A TargetD member with a nontrivial character**: `chi4Member` meets `TargetD 2 1 1`
(value `≡ 2 (mod 4)` at every prime, `≡ 0 (mod 4)` whenever `ω(n) ≥ 2`). -/
theorem chi4Member_targetD : TargetD 2 1 1 chi4Member := by
  rw [chi4Member_eq]
  refine ⟨fun q hq => ⟨1, by norm_num, ?_⟩, fun n hn => ?_⟩
  · rw [B4, prodPrimeFactors_apply hq.ne_zero, hq.primeFactors, prod_singleton]
    simpa using core_L4_prime_mod4 hq
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [B4, prodPrimeFactors_apply hn0]
    have h2 : ∀ q ∈ n.primeFactors, (2 : ℤ) ∣ core L4 q := by
      intro q hq
      have := core_L4_prime_mod4 (Nat.prime_of_mem_primeFactors hq)
      obtain ⟨t, ht⟩ := this
      exact ⟨2 * t + 1, by linarith⟩
    have hd := prod_dvd_prod_of_dvd _ _ h2
    rw [prod_const] at hd
    have hc : 2 ≤ n.primeFactors.card := by
      rw [M2L3.card_primeFactors_eq_omega]; exact hn
    have : (2 : ℤ) ^ (1 + 1) ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hc
    exact this.trans hd

/-- **The twisted lower bound is attained by a member with a nontrivial character.** Every member
with the single core `L4` (factors `n` and `χ₄`, signed degree `2`), any coefficient and any
correction `≡ 0 (mod 2^(v+k))` on squarefree `m > 1`, meeting `TargetD 2 v k`, has `k ≤ 1`
(`thmH_twisted`); and `chi4Member` meets `TargetD 2 1 1`. So
`max {k | ∃ v, TargetD 2 v k (member)} = 1 = v₂(2)`. -/
theorem chi4_bound_attained :
    (∀ (c : Unit → ℤ) (h : Unit → ArithmeticFunction ℤ) (v k : ℕ),
      (∀ m, Squarefree m → 1 < m → (2 : ℤ) ^ (v + k) ∣ h () m) →
      TargetD 2 v k (M2L2.famI ({()} : Finset Unit) c (fun _ => core L4) h) → k ≤ 1) ∧
    TargetD 2 1 1 chi4Member ∧ (∀ m, Squarefree m → 1 < m → h4 m = 0) ∧
    ZMod.χ₄ ≠ 1 := by
  refine ⟨fun c h v k hh hf => ?_, chi4Member_targetD, fun m hm hm1 => h4_squarefree hm hm1,
    chi4_nontrivial⟩
  have := thmH_twisted 2 ({()} : Finset Unit) (fun _ => L4) c h
    (fun i _ F hF => by
      simp only [L4, List.mem_cons, List.mem_nil_iff, or_false] at hF
      rcases hF with rfl | rfl <;> simp [chi4F, powF])
    (fun i hi m hm hm1 => by cases i; exact hh m hm hm1) hf
  simpa [sdeg_L4, padicValInt] using this

theorem chi4_isGreatest :
    IsGreatest {k | ∃ v, TargetD 2 v k chi4Member} 1 := by
  refine ⟨⟨1, chi4Member_targetD⟩, fun k ⟨v, hk⟩ => ?_⟩
  exact chi4_bound_attained.1 (fun _ => 1) (fun _ => h4) v k
    (fun m hm hm1 => by rw [h4_squarefree hm hm1]; exact dvd_zero _) hk

end Chi4

end M2L4
