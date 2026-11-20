/-
  Seat M2L5, item 3: small closures of the round 4 audit list.
  (a) the (H6) power series of round 4 are the local factors of round 1's corrections `hcorr`;
  (b) (H9) and (H10) with the explicit table weights of round 4;
  (c) the multi-correction reduction for Theorem J;
  (d) a `TargetDO` member with a nontrivial character over `ℤ[i]` and over `𝓞 ℚ(ζ_N)`;
  (e) Theorem B's finite-domain remark and the `F_{p²}` counterexample `f = α δ`;
  (f) Theorem D's meta-claim: our conjectured class, and the round 3 mod 9 filter lies outside it.
-/
import Mathlib
import M2Parity
import M2Tables
import M2ConstructO
import M2Frobenius
import M2ThetaJ2

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma ArithmeticFunction.Moebius
  ArithmeticFunction.omega ArithmeticFunction.Omega

namespace M2L5

/-! ## (a) (H6) is the local factor of `hcorr` -/

section HcorrLink

/-- The local series `∑_e f(q^e) t^e` of an arithmetic function at `q`. -/
noncomputable def loc (q : ℕ) (f : ArithmeticFunction ℤ) : PowerSeries ℤ := PowerSeries.mk fun e => f (q ^ e)

lemma coeff_loc (q : ℕ) (f : ArithmeticFunction ℤ) (e : ℕ) : PowerSeries.coeff e (loc q f) = f (q ^ e) := by
  simp [loc]

variable {q : ℕ} (hq : q.Prime)
include hq

lemma loc_mul (f g : ArithmeticFunction ℤ) : loc q (f * g) = loc q f * loc q g := by
  ext e
  rw [coeff_loc, M2L3.mul_apply_prime_pow _ _ hq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_loc]

lemma loc_pow (f : ArithmeticFunction ℤ) (n : ℕ) : loc q (f ^ n) = loc q f ^ n := by
  induction n with
  | zero =>
    ext e
    rw [pow_zero, pow_zero, coeff_loc, PowerSeries.coeff_one, ArithmeticFunction.one_apply]
    simp [hq.one_lt.ne']
  | succ n ih => rw [pow_succ, pow_succ, loc_mul hq, ih]

lemma loc_zeta : loc q (ζ : ArithmeticFunction ℤ) = M2L4.geomS := by
  ext e
  rw [coeff_loc, M2L4.geomS_coeff]
  simp [natCoe_apply, zeta_apply, hq.ne_zero]

lemma loc_moebius : loc q (μ : ArithmeticFunction ℤ) = 1 - PowerSeries.X := by
  ext e
  rw [coeff_loc]
  rcases e with _ | _ | e
  · simp
  · simp [moebius_apply_prime hq]
  · rw [moebius_apply_prime_pow hq (by omega)]
    simp [PowerSeries.coeff_X]

lemma loc_zinv (z : ℤ) : loc q (M2L.zinv z) = ((M2L4.oneSubX ^ z : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) := by
  unfold M2L.zinv
  split_ifs with hz
  · rw [loc_pow hq, loc_moebius hq]
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    simp [M2L4.oneSubX]
  · rw [loc_pow hq, loc_zeta hq]
    obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (by omega : z ≤ 0)
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, M2L4.oneSubX_inv]
    simp

lemma loc_Bz (z : ℤ) : loc q (M2L.Bz z) = 1 + PowerSeries.C z * PowerSeries.X * M2L4.geomS := by
  ext e
  rw [coeff_loc, M2L4.B_series_coeff]
  rcases e with _ | e
  · simp [M2L.Bz_apply z one_ne_zero]
  · rw [M2L.Bz_apply z (pow_ne_zero _ hq.ne_zero), cardDistinctFactors_apply_prime_pow hq (by omega)]
    simp

/-- **(H6) linked to round 1**: the local series of `hcorr z` at every prime is the (H6) series. -/
theorem loc_hcorr (z : ℤ) : loc q (M2L.hcorr z) = M2L4.H6series z := by
  rw [M2L.hcorr, loc_mul hq, loc_zinv hq, loc_Bz hq]
  have e : M2L4.H6series z = (1 + PowerSeries.C z * PowerSeries.X * M2L4.geomS)
      * ((M2L4.oneSubX ^ z : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) := by
    rw [← M2L4.H7_series z, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, mul_one]
  rw [e, mul_comm]

/-- **(H6) at prime powers**: `hcorr z (q^e)` is the `t^e` coefficient of `(1 + (z-1) t)(1 - t)^(z-1)`,
for every integer `z`, prime `q` and `e ≥ 0`. -/
theorem hcorr_prime_pow_eq_H6 (z : ℤ) (e : ℕ) :
    M2L.hcorr z (q ^ e) = PowerSeries.coeff e (M2L4.H6series z) := by
  rw [← loc_hcorr hq z, coeff_loc]

end HcorrLink

/-! ## (b) (H9) and (H10) with the table weights -/

section H9H10

open M2L

lemma mom_omega_split {T : Finset ℤ} {a : ℤ → ℤ} {C : ℤ} (h1 : mom T a 1 = C) {n : ℕ} (hn : 0 < n) :
    mom T a (ω n) = (if n = 1 then ∑ z ∈ T, a z else 0) + C * (if IsPrimePow n then 1 else 0)
      + (if 2 ≤ ω n then mom T a (ω n) else 0) := by
  by_cases hn1 : n = 1
  · subst hn1; simp [mom, not_isPrimePow_one]
  have h0 : ω n ≠ 0 := by rw [Ne, cardDistinctFactors_eq_zero]; omega
  by_cases hpp : IsPrimePow n
  · have : ω n = 1 := cardDistinctFactors_eq_one_iff.2 hpp
    simp [hn1, hpp, this, h1]
  · have h1' : ω n ≠ 1 := fun h => hpp (cardDistinctFactors_eq_one_iff.1 h)
    simp [hn1, hpp, show 2 ≤ ω n by omega]

lemma sum_roots_split {x : ℕ} (hx : 1 ≤ x) :
    ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (M2L4.iroot j x) : ℤ)
      = Nat.primeCounting x + ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting (M2L4.iroot j x) : ℤ) := by
  by_cases hx1 : x = 1
  · subst hx1; simp
  · have : Icc 1 (Nat.log 2 x) = insert 1 (Icc 2 (Nat.log 2 x)) := by
      have hl : 1 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by omega)
      ext j; simp only [mem_Icc, mem_insert]; omega
    rw [this, sum_insert (by simp), M2L4.iroot_one]

/-- The exact identity behind (H9) for a checked row (`s_1 = C`, `s_r = 0` for `2 ≤ r ≤ |T|`):
`∑_{n ≤ x} F_T(n) = ∑_z a_z + C ∑_{j ≤ log₂ x} π(⌊x^(1/j)⌋) + C (∏ z) K` for some integer `K`. -/
theorem H9_exact {T : Finset ℤ} (hne : T.Nonempty) {a : ℤ → ℤ} {C : ℤ} (hrow : M2L4.RowOK T a C)
    {x : ℕ} (hx : 1 ≤ x) : ∃ K : ℤ,
    ∑ n ∈ Ioc 0 x, fam T a zpowZeta hcorr n
      = ∑ z ∈ T, a z + C * ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (M2L4.iroot j x) : ℤ)
        + C * (∏ z ∈ T, z) * K := by
  have hdiv : C * ∏ z ∈ T, z ∣ ∑ n ∈ Ioc 0 x, (if 2 ≤ ω n then mom T a (ω n) else 0) := by
    apply dvd_sum
    intro n _
    split_ifs with h
    · have := M2L4.mom_dvd_of_vanish T hne a hrow.vanish h
      rwa [hrow.1] at this
    · exact dvd_zero _
  obtain ⟨K, hK⟩ := hdiv
  refine ⟨K, ?_⟩
  have e : ∀ n ∈ Ioc 0 x, fam T a zpowZeta hcorr n
      = (if n = 1 then ∑ z ∈ T, a z else 0) + C * (if IsPrimePow n then 1 else 0)
        + (if 2 ≤ ω n then mom T a (ω n) else 0) := by
    intro n hn
    have hn0 := (mem_Ioc.1 hn).1
    rw [fam_hcorr_apply T a (by omega)]
    exact mom_omega_split hrow.1 hn0
  rw [sum_congr rfl e, sum_add_distrib, sum_add_distrib, ← mul_sum, hK, sum_ite_eq',
    card_primePow_eq_sum, if_pos (mem_Ioc.2 ⟨by omega, hx⟩)]

/-- **(H9)** for a checked row: `∑_{n ≤ x} F_T(n) ≡ ∑_z a_z + C ∑_{j} π(⌊x^(1/j)⌋) (mod C ∏ z)`,
hence modulo `C p^k` whenever `p^k ∣ ∏ z`. -/
def H9Row (T : Finset ℤ) (a : ℤ → ℤ) (C : ℤ) (p k : ℕ) : Prop :=
  ∀ x : ℕ, 1 ≤ x →
    ∑ n ∈ Ioc 0 x, fam T a zpowZeta hcorr n
      ≡ ∑ z ∈ T, a z + C * ∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (M2L4.iroot j x) : ℤ)
        [ZMOD C * (p : ℤ) ^ k]

/-- **(H10)** for a checked row: the numerator is exactly divisible by `C` and
`π(x) ≡ (∑_{n ≤ x} F_T(n) - ∑_z a_z)/C - ∑_{2 ≤ j ≤ log₂ x} π(⌊x^(1/j)⌋) (mod p^k)`. -/
def H10Row (T : Finset ℤ) (a : ℤ → ℤ) (C : ℤ) (p k : ℕ) : Prop :=
  ∀ x : ℕ, 1 ≤ x →
    C ∣ (∑ n ∈ Ioc 0 x, fam T a zpowZeta hcorr n - ∑ z ∈ T, a z) ∧
    (Nat.primeCounting x : ℤ)
      ≡ (∑ n ∈ Ioc 0 x, fam T a zpowZeta hcorr n - ∑ z ∈ T, a z) / C
        - ∑ j ∈ Icc 2 (Nat.log 2 x), (Nat.primeCounting (M2L4.iroot j x) : ℤ) [ZMOD (p : ℤ) ^ k]

theorem H9_H10_of_row {T : Finset ℤ} (hne : T.Nonempty) {a : ℤ → ℤ} {C : ℤ} (hrow : M2L4.RowOK T a C)
    (hC : C ≠ 0) {p k : ℕ} (hk : (p : ℤ) ^ k ∣ ∏ z ∈ T, z) : H9Row T a C p k ∧ H10Row T a C p k := by
  obtain ⟨m, hm⟩ := hk
  constructor
  · intro x hx
    obtain ⟨K, hK⟩ := H9_exact hne hrow hx
    rw [hK, hm, Int.modEq_iff_dvd]
    exact ⟨-(m * K), by ring⟩
  · intro x hx
    obtain ⟨K, hK⟩ := H9_exact hne hrow hx
    have hnum : ∑ n ∈ Ioc 0 x, fam T a zpowZeta hcorr n - ∑ z ∈ T, a z
        = C * (∑ j ∈ Icc 1 (Nat.log 2 x), (Nat.primeCounting (M2L4.iroot j x) : ℤ)
          + (p : ℤ) ^ k * (m * K)) := by
      rw [hK, hm]; ring
    refine ⟨⟨_, hnum⟩, ?_⟩
    rw [hnum, Int.mul_ediv_cancel_left _ hC, sum_roots_split hx, Int.modEq_iff_dvd]
    exact ⟨m * K, by ring⟩

/-- **(H9), (H10) instantiated with every row of the round 4 coefficient tables**, at the levels of
`M2L4.rows_targetD`, for every `x ≥ 1`. -/
theorem rows_H9_H10 :
    (H9Row (cheapNodes 2) M2L4.P2 2 2 1 ∧ H10Row (cheapNodes 2) M2L4.P2 2 2 1) ∧
    (H9Row (cheapNodes 3) M2L4.P3 6 3 1 ∧ H10Row (cheapNodes 3) M2L4.P3 6 3 1) ∧
    (H9Row (cheapNodes 4) M2L4.P4 12 2 3 ∧ H10Row (cheapNodes 4) M2L4.P4 12 2 3) ∧
    (H9Row (cheapNodes 6) M2L4.P6 60 2 4 ∧ H10Row (cheapNodes 6) M2L4.P6 60 2 4) ∧
    (H9Row (cheapNodes 6) M2L4.P6 60 3 2 ∧ H10Row (cheapNodes 6) M2L4.P6 60 3 2) ∧
    (H9Row (cheapNodes 9) M2L4.P9 2520 3 4 ∧ H10Row (cheapNodes 9) M2L4.P9 2520 3 4) ∧
    (H9Row (signedNodes 2) M2L4.S2 12 2 2 ∧ H10Row (signedNodes 2) M2L4.S2 12 2 2) ∧
    (H9Row (signedNodes 3) M2L4.S3 60 3 2 ∧ H10Row (signedNodes 3) M2L4.S3 60 3 2) ∧
    (H9Row (signedNodes 4) M2L4.S4 840 2 6 ∧ H10Row (signedNodes 4) M2L4.S4 840 2 6) ∧
    (H9Row (signedNodes 6) M2L4.S6 27720 3 4 ∧ H10Row (signedNodes 6) M2L4.S6 27720 3 4) := by
  obtain ⟨p2, p3, p4, p6, p9⟩ := M2L4.rows_positive
  obtain ⟨s2, s3, s4, s6⟩ := M2L4.rows_signed
  refine ⟨H9_H10_of_row (M2L4.cheap_nonempty 2 (by norm_num)) p2 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.cheap_nonempty 3 (by norm_num)) p3 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.cheap_nonempty 4 (by norm_num)) p4 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.cheap_nonempty 6 (by norm_num)) p6 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.cheap_nonempty 6 (by norm_num)) p6 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.cheap_nonempty 9 (by norm_num)) p9 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.signed_nonempty 2 (by norm_num)) s2 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.signed_nonempty 3 (by norm_num)) s3 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.signed_nonempty 4 (by norm_num)) s4 (by norm_num) (by decide),
    H9_H10_of_row (M2L4.signed_nonempty 6 (by norm_num)) s6 (by norm_num) (by decide)⟩

end H9H10

/-! ## (c) Theorem J: the multi-correction reduction -/

section ThetaMulti

lemma mul_apply_squarefree {θ h : ArithmeticFunction ℤ} (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0)
    {n : ℕ} (hn : Squarefree n) : (θ * h) n = θ n * h 1 := by
  have hn0 : n ≠ 0 := hn.ne_zero
  rw [mul_apply, sum_eq_single (n, 1)]
  · rintro ⟨a, b⟩ hab hne
    rw [Nat.mem_divisorsAntidiagonal] at hab
    have hb : b ∣ n := ⟨a, by rw [← hab.1]; ring⟩
    have hb1 : b ≠ 1 := by
      rintro rfl; apply hne
      have : a = n := by simpa using hab.1
      rw [this]
    simp [hh b (hn.squarefree_of_dvd hb) hb1]
  · intro h; exfalso; apply h; simp [Nat.mem_divisorsAntidiagonal, hn0]

lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    fun a ha => (hs a ha).squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hs a ha) (hs b hb)).2 hab

/-- **Theorem J with several corrections** (the multi-correction reduction): a finite combination
`∑_i c_i (θ_i * h_i)`, each `θ_i` of the slice form `2^e 3^t θ_i = A_i 2^r + B_i (-1)^r` on products of
`r ≥ 1` distinct primes of an infinite prime set `S`, each `h_i` vanishing on squarefree `n > 1`,
cannot be nonzero mod `3^m` at every prime of `S` while vanishing mod `3^m` on every product of at
least two distinct primes of `S`. (On squarefree arguments it equals the single theta combination
`∑_i c_i h_i(1) θ_i` with the trivial correction, to which round 4's `thetaJ_slice` applies.) -/
theorem thetaJ_multi {ι : Type*} (m e t : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (I : Finset ι) (c : ι → ℤ) (theta : ι → ArithmeticFunction ℤ) (A B : ι → ℤ)
    (hval : ∀ i ∈ I, ∀ s : Finset ℕ, ↑s ⊆ S → 1 ≤ s.card →
      2 ^ e * 3 ^ t * theta i (∏ p ∈ s, p) = A i * 2 ^ s.card + B i * (-1) ^ s.card)
    (h : ι → ArithmeticFunction ℤ) (hh : ∀ i ∈ I, ∀ n, Squarefree n → n ≠ 1 → h i n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ M2L2.famI I c theta h q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ M2L2.famI I c theta h (∏ p ∈ s, p))) := by
  set th : ArithmeticFunction ℤ := M2L2.famI I (fun i => c i * h i 1) theta (fun _ => 1)
  have th_apply : ∀ n, th n = ∑ i ∈ I, c i * h i 1 * theta i n := by
    intro n
    rw [M2L2.famI_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_one]
  have hsq : ∀ n, Squarefree n → M2L2.famI I c theta h n = (th * 1) n := by
    intro n hn
    rw [mul_one, th_apply, M2L2.famI_apply]
    refine sum_congr rfl fun i hi => ?_
    rw [mul_apply_squarefree (hh i hi) hn]; ring
  have hval' : ∀ s : Finset ℕ, ↑s ⊆ S → 1 ≤ s.card →
      2 ^ e * 3 ^ t * th (∏ p ∈ s, p)
        = (∑ i ∈ I, c i * h i 1 * A i) * 2 ^ s.card + (∑ i ∈ I, c i * h i 1 * B i) * (-1) ^ s.card := by
    intro s hs hc
    rw [th_apply, mul_sum, sum_mul, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    have := hval i hi s hs hc
    linear_combination (c i * h i 1) * this
  have key := M2L4.thetaJ_slice m e t S hS hinf th _ _ hval' 1
    (fun n _ hn => by rw [ArithmeticFunction.one_apply, if_neg hn])
  rintro ⟨h1, h2⟩
  apply key
  refine ⟨fun q hq => ?_, fun s hs hc => ?_⟩
  · rw [← hsq q (hS q hq).squarefree]; exact h1 q hq
  · rw [← hsq _ (squarefree_prod_primes fun p hp => hS p (hs hp))]; exact h2 s hs hc

end ThetaMulti

/-! ## (d) A `TargetDO` member with a nontrivial character over `ℤ[i]` and `𝓞 ℚ(ζ_N)` -/

section Chi4O

/-- Over any domain of characteristic zero, the cast of round 4's `chi4Member` is the `famO` member
with the cast core `n · χ₄(n)` and the cast correction `h4`. -/
theorem chi4Member_cast_famO (O : Type*) [CommRing O] :
    ((M2L4.chi4Member : ArithmeticFunction ℤ) : ArithmeticFunction O)
      = M2L2.famO ({()} : Finset Unit) (fun _ => (1 : O))
          (fun _ => ((M2L2.core M2L4.L4 : ArithmeticFunction ℤ) : ArithmeticFunction O))
          (fun _ => ((M2L4.h4 : ArithmeticFunction ℤ) : ArithmeticFunction O)) := by
  ext n
  have e1 : M2L2.famO ({()} : Finset Unit) (fun _ => (1 : O))
      (fun _ => ((M2L2.core M2L4.L4 : ArithmeticFunction ℤ) : ArithmeticFunction O))
      (fun _ => ((M2L4.h4 : ArithmeticFunction ℤ) : ArithmeticFunction O)) n
      = (((M2L2.core M2L4.L4 : ArithmeticFunction ℤ) : ArithmeticFunction O)
          * ((M2L4.h4 : ArithmeticFunction ℤ) : ArithmeticFunction O)) n := by
    show ∑ i ∈ ({()} : Finset Unit), (1 : O) * _ = _
    simp
  rw [e1, ← intCoe_mul, intCoe_apply, intCoe_apply, M2L4.chi4Member, M2L2.famI_apply]
  simp

/-- **A `TargetDO` member with a nontrivial character over the Gaussian integers** `ℤ[i]`:
the cast of `chi4Member` (core `n χ₄(n)`, `χ₄ ≠ 1`) meets `TargetDO 2 1 1`. -/
theorem chi4Member_targetDO_gaussian :
    M2L2.TargetDO (O := GaussianInt) 2 1 1
      ((M2L4.chi4Member : ArithmeticFunction ℤ) : ArithmeticFunction GaussianInt) :=
  M2L4.targetDO_of_targetD 2 M2L4.chi4Member_targetD

open NumberField in
/-- The same over the ring of integers of every cyclotomic field `ℚ(ζ_N)`. -/
theorem chi4Member_targetDO_cyclotomic (N : ℕ) [NeZero N] :
    M2L2.TargetDO (O := 𝓞 (CyclotomicField N ℚ)) 2 1 1
      ((M2L4.chi4Member : ArithmeticFunction ℤ) : ArithmeticFunction (𝓞 (CyclotomicField N ℚ))) :=
  M2L4.targetDO_of_targetD 2 M2L4.chi4Member_targetD

end Chi4O

/-! ## (e) The `F_{p²}` counterexample and Theorem B's finite-domain remark -/

section FrobCounter

/-- Over a commutative ring of characteristic `p`, if `α^p ≠ α` then `f = α δ` has
`f^(*p) ≠ E_p(f)`, while `f^(*p) = E_p(Frob ∘ f)` (round 4's general identity). -/
theorem frob_alpha_delta {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] (α : R)
    (hα : α ^ p ≠ α) :
    (α • (1 : ArithmeticFunction R)) ^ p ≠ M2L4.Ek p (α • (1 : ArithmeticFunction R)) ∧
    (α • (1 : ArithmeticFunction R)) ^ p = M2L4.Ek p (M2L4.frobF p (α • (1 : ArithmeticFunction R))) := by
  refine ⟨fun h => hα ?_, M2L4.frobenius_dirichlet p _⟩
  have := congrArg (fun F : ArithmeticFunction R => F 1) h
  rw [smul_pow, one_pow, ArithmeticFunction.smul_map, ArithmeticFunction.one_one, smul_eq_mul,
    mul_one] at this
  rw [this, show (1 : ℕ) = 1 ^ p by simp, M2L4.Ek_pow hp.out.pos, ArithmeticFunction.smul_map,
    ArithmeticFunction.one_one, smul_eq_mul, mul_one]

/-- In `F_{p²}` (`GaloisField p 2`) some `α` has `α^p ≠ α`. -/
theorem exists_pow_ne_self (p : ℕ) [hp : Fact p.Prime] : ∃ α : GaloisField p 2, α ^ p ≠ α := by
  classical
  by_contra h
  push Not at h
  let _ := Fintype.ofFinite (GaloisField p 2)
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 (by norm_num)
  set P : Polynomial (GaloisField p 2) := Polynomial.X ^ p - Polynomial.X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp.out.one_lt
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt
  have hsub : (Finset.univ : Finset (GaloisField p 2)) ⊆ P.roots.toFinset := by
    intro a _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [P, h a]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, hcard] at h1
  have h2 := h1.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P))
  rw [hdeg] at h2
  have := hp.out.two_le
  nlinarith

/-- **The `F_{p²}` counterexample** (A19 section 2, correction to the background): for every prime
`p` there is `α ∈ F_{p²}` such that `f = α δ` satisfies `f^(*p) ≠ E_p(f)`; the general identity is
`f^(*p) = E_p(Frob ∘ f)`. -/
theorem Fp2_counterexample (p : ℕ) [Fact p.Prime] :
    ∃ α : GaloisField p 2,
      (α • (1 : ArithmeticFunction (GaloisField p 2))) ^ p
          ≠ M2L4.Ek p (α • (1 : ArithmeticFunction (GaloisField p 2))) ∧
      (α • (1 : ArithmeticFunction (GaloisField p 2))) ^ p
          = M2L4.Ek p (M2L4.frobF p (α • (1 : ArithmeticFunction (GaloisField p 2)))) := by
  obtain ⟨α, hα⟩ := exists_pow_ne_self p
  exact ⟨α, frob_alpha_delta p α hα⟩

/-- Weights of the finite-domain example: `a_1 = -3`, `a_2 = 3`. -/
def cB (z : ℤ) : ℤ := if z = 1 then -3 else 3

/-- The finite-domain example `F = -3 B_1 + 3 B_2 = ∑_z a_z (d_z * h_z)` on the nodes `{1, 2}`. -/
noncomputable def FB : ArithmeticFunction ℤ := M2L.fam ({1, 2} : Finset ℤ) cB M2L.zpowZeta M2L.hcorr

lemma FB_apply {n : ℕ} (hn : n ≠ 0) : FB n = -3 + 3 * 2 ^ ω n := by
  rw [FB, M2L.fam_hcorr_apply _ _ hn, M2L.mom]
  simp [cB]

lemma omega_thirty : ω 30 = 3 := by
  have h15 : ω 15 = 2 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, cardDistinctFactors_mul (by norm_num),
      cardDistinctFactors_apply_prime Nat.prime_three, cardDistinctFactors_apply_prime (by norm_num)]
  rw [show (30 : ℕ) = 2 * 15 by norm_num, cardDistinctFactors_mul (by norm_num),
    cardDistinctFactors_apply_prime Nat.prime_two, h15]

/-- **Theorem B's finite-domain remark** (`p = 3`, target `D` modulo `9`): the integral member
`F = -3 B_1 + 3 B_2` has value `3 = 3 · 1` at every prime and value `9 ≡ 0 (mod 9)` at every `n`
with `ω(n) = 2`, so it meets the target on every domain where `ω(n) ≤ 2` (e.g. `n ≤ 29`); yet no
degree is divisible by `3` (so none has `v_3(z) = 1`, the conclusion of Theorem B fails), and the
full target fails at `n = 30` (`ω = 3`, value `21`). So Theorem B certifies nothing from `ω(n) ≤ r`. -/
theorem thmB_finite_domain :
    (∀ q : ℕ, q.Prime → FB q = 3 * 1) ∧
    (∀ n : ℕ, ω n = 2 → (9 : ℤ) ∣ FB n) ∧
    (∀ z ∈ ({1, 2} : Finset ℤ), ¬ (3 : ℤ) ∣ z) ∧
    FB 30 = 21 ∧ ¬ (9 : ℤ) ∣ FB 30 ∧ ¬ M2L.TargetD 3 1 1 FB := by
  have h30 : FB 30 = 21 := by rw [FB_apply (by norm_num), omega_thirty]; norm_num
  refine ⟨fun q hq => ?_, fun n hn => ?_, by decide, h30, by rw [h30]; decide, fun hT => ?_⟩
  · rw [FB_apply hq.ne_zero, cardDistinctFactors_apply_prime hq]; norm_num
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rw [FB_apply hn0, hn]; norm_num
  · have := hT.2 30 (by rw [omega_thirty]; norm_num)
    rw [h30] at this; norm_num at this

end FrobCounter

/-! ## (f) Theorem D's meta-claim: our conjectured class excludes the round 3 mod 9 filter -/

section ConjD

/-- A degree-3 core of "d_3 type": three factors `ℓ(χ_i, k_i)`, each equal to `ζ` up to a twist
`w_i(q) = χ_i(q) q^(k_i)` with `w_i(q) ≡ 1 (mod 3)` at every prime `q` (our Q2.2 conjecture, A19 Q2). -/
def DType3 (G : ArithmeticFunction ℤ) : Prop :=
  ∃ (N1 N2 N3 k1 k2 k3 : ℕ) (χ1 : DirichletCharacter ℤ N1) (χ2 : DirichletCharacter ℤ N2)
    (χ3 : DirichletCharacter ℤ N3),
    (∀ q : ℕ, q.Prime → M2L2.ell χ1 k1 q ≡ 1 [ZMOD 3]) ∧
    (∀ q : ℕ, q.Prime → M2L2.ell χ2 k2 q ≡ 1 [ZMOD 3]) ∧
    (∀ q : ℕ, q.Prime → M2L2.ell χ3 k3 q ≡ 1 [ZMOD 3]) ∧
    G = M2L2.ell χ1 k1 * M2L2.ell χ2 k2 * M2L2.ell χ3 k3

/-- **Our conjectured class**, made precise: finite integral combinations `∑_i c_i (G_i * h_i)` of
d_3-type cores `G_i` with multiplicative corrections `h_i` vanishing at every prime (squarefull
support). -/
def ConjClass (f : ℕ → ℤ) : Prop :=
  ∃ (ι : Type) (I : Finset ι) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ),
    (∀ i ∈ I, DType3 (G i)) ∧ (∀ i ∈ I, (h i).IsMultiplicative ∧ ∀ q, q.Prime → h i q = 0) ∧
    ∀ n, f n = M2L2.famI I c G h n

/-- A twist `w(q) = χ(q) q^k ≡ 1 (mod 3)` is exactly `1` at `q = 3`. -/
lemma ell_three {N k : ℕ} (χ : DirichletCharacter ℤ N) (h : M2L2.ell χ k 3 ≡ 1 [ZMOD 3]) :
    M2L2.ell χ k 3 = 1 := by
  rw [M2L2.ell_apply χ k (by norm_num)] at h ⊢
  have hval : χ ((3 : ℕ) : ZMod N) = 1 ∨ χ ((3 : ℕ) : ZMod N) = -1 ∨ χ ((3 : ℕ) : ZMod N) = 0 := by
    by_cases hu : IsUnit ((3 : ℕ) : ZMod N)
    · rcases Int.isUnit_iff.1 (hu.map χ) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (MulChar.map_nonunit χ hu))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, mul_one] at h ⊢
    rcases hval with h1 | h1 | h1 <;> rw [h1] at h ⊢ <;> simp_all [Int.ModEq]
  · exfalso
    have h3 : (3 : ℤ) ∣ χ ((3 : ℕ) : ZMod N) * ((3 : ℕ) : ℤ) ^ k :=
      Dvd.dvd.mul_left (dvd_pow_self _ hk.ne') _
    have := (Int.ModEq.dvd h.symm)
    have h31 : (3 : ℤ) ∣ 1 := by
      have := dvd_sub h3 this
      simp at this
    omega

lemma DType3_one {G : ArithmeticFunction ℤ} (hG : DType3 G) : G.IsMultiplicative ∧ G 3 = 3 := by
  obtain ⟨N1, N2, N3, k1, k2, k3, χ1, χ2, χ3, h1, h2, h3, rfl⟩ := hG
  have m1 := M2L2.ell_mult χ1 k1
  have m2 := M2L2.ell_mult χ2 k2
  have m3 := M2L2.ell_mult χ3 k3
  refine ⟨(m1.mul m2).mul m3, ?_⟩
  rw [M2L3.mul_apply_prime (m1.mul m2) m3 Nat.prime_three, M2L3.mul_apply_prime m1 m2 Nat.prime_three,
    ell_three χ1 (h1 3 Nat.prime_three), ell_three χ2 (h2 3 Nat.prime_three),
    ell_three χ3 (h3 3 Nat.prime_three)]
  norm_num

/-- Every member of the class has `f(3) = 3 f(1)`. -/
theorem ConjClass_three {f : ℕ → ℤ} (hf : ConjClass f) : f 3 = 3 * f 1 := by
  obtain ⟨ι, I, c, G, h, hG, hh, hfe⟩ := hf
  rw [hfe, hfe, M2L2.famI_apply, M2L2.famI_apply, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  obtain ⟨hGm, hG3⟩ := DType3_one (hG i hi)
  obtain ⟨hhm, hh0⟩ := hh i hi
  rw [M2L3.mul_apply_prime hGm hhm Nat.prime_three, hG3, hh0 3 Nat.prime_three,
    (hGm.mul hhm).map_one]
  ring

/-- **Theorem D's meta-claim**: the round 3 mod 9 filter `F = 3A - 2B` (cores with shifts `0, 2, 4`)
is not in our conjectured class: `F(1) = 1` but `F(3) = F(3^e) = 273 ≠ 3`. -/
theorem F9_not_ConjClass : ¬ ConjClass M2L3.F9 := by
  intro hf
  have h := ConjClass_three hf
  have h1 : M2L3.F9 1 = 1 := M2L3.Ffun_one 3 _
  have h3 : M2L3.F9 3 = 273 := by
    have := M2L3.Ffun_prime_pow_eq 3 M2L3.g9 Nat.prime_three (e := 1) one_pos
    rw [pow_one] at this
    show M2L3.Ffun 3 M2L3.g9 3 = 273
    rw [this]; simp [M2L3.g9]
  rw [h1, h3] at h
  norm_num at h

theorem F9_three_pow (e : ℕ) (he : 0 < e) : M2L3.F9 (3 ^ e) = 273 := by
  show M2L3.Ffun 3 M2L3.g9 (3 ^ e) = 273
  rw [M2L3.Ffun_prime_pow_eq 3 M2L3.g9 Nat.prime_three he]; simp [M2L3.g9]

end ConjD

end M2L5
