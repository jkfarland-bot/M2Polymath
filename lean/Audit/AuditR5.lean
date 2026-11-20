import M2BlockS
import M2Parity
import M2Closures
import M2TupleN

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace Audit5

/-! ## (A) DType3 collapses: every twist allowed by DType3 is the constant 1 on n >= 1. -/

lemma ell_twist_trivial {N k : ℕ} (χ : DirichletCharacter ℤ N)
    (h : ∀ q : ℕ, q.Prime → M2L2.ell χ k q ≡ 1 [ZMOD 3]) :
    k = 0 ∧ ∀ q : ℕ, q.Prime → M2L2.ell χ k q = 1 := by
  have h3 := M2L5.ell_three χ (h 3 Nat.prime_three)
  rw [M2L2.ell_apply χ k (by norm_num)] at h3
  have hk : k = 0 := by
    by_contra hk
    have : (3 : ℤ) ∣ χ ((3 : ℕ) : ZMod N) * ((3 : ℕ) : ℤ) ^ k :=
      Dvd.dvd.mul_left (dvd_pow_self _ hk) _
    rw [h3] at this; omega
  refine ⟨hk, fun q hq => ?_⟩
  have hq' := h q hq
  subst hk
  rw [M2L2.ell_apply χ 0 hq.ne_zero, pow_zero, mul_one] at hq' ⊢
  have hval : χ ((q : ℕ) : ZMod N) = 1 ∨ χ ((q : ℕ) : ZMod N) = -1 ∨ χ ((q : ℕ) : ZMod N) = 0 := by
    by_cases hu : IsUnit ((q : ℕ) : ZMod N)
    · rcases Int.isUnit_iff.1 (hu.map χ) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (MulChar.map_nonunit χ hu))
  rcases hval with h1 | h1 | h1 <;> rw [h1] at hq' ⊢ <;> simp_all [Int.ModEq]

lemma ell_eq_zeta {N k : ℕ} (χ : DirichletCharacter ℤ N)
    (h : ∀ q : ℕ, q.Prime → M2L2.ell χ k q ≡ 1 [ZMOD 3]) :
    M2L2.ell χ k = ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) := by
  obtain ⟨_, hq⟩ := ell_twist_trivial χ h
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (M2L2.ell_mult χ k) _
    (isMultiplicative_zeta.natCast)]
  intro p e hp
  have hpow : ∀ e : ℕ, M2L2.ell χ k (p ^ e) = 1 := by
    intro e
    induction e with
    | zero => simp [M2L2.ell_one]
    | succ e ih => rw [pow_succ, M2L2.ell_mul_apply, ih, hq p hp, one_mul]
  rw [hpow e, natCoe_apply, zeta_apply, if_neg (pow_ne_zero _ hp.ne_zero)]; simp

/-- Every DType3 core is exactly d_3 = zeta * zeta * zeta (no power twist, no nontrivial character). -/
theorem DType3_iff_d3 (G : ArithmeticFunction ℤ) :
    M2L5.DType3 G → G = ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) ^ 3 := by
  rintro ⟨N1, N2, N3, k1, k2, k3, χ1, χ2, χ3, h1, h2, h3, rfl⟩
  rw [ell_eq_zeta χ1 h1, ell_eq_zeta χ2 h2, ell_eq_zeta χ3 h3]; ring

/-! ## (B) Non-vacuity: d_3 itself is in ConjClass. -/

theorem d3_in_ConjClass :
    M2L5.ConjClass (fun n => (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) ^ 3) n) := by
  refine ⟨Unit, {()}, fun _ => 1, fun _ => M2L2.ell (1 : DirichletCharacter ℤ 1) 0 ^ 3,
    fun _ => 1, ?_, ?_, ?_⟩
  · intro i _
    refine ⟨1, 1, 1, 0, 0, 0, 1, 1, 1, ?_, ?_, ?_, by ring⟩ <;>
    · intro q hq; rw [M2L2.ell_trivial_apply 0 hq.ne_zero]; simp
  · intro i _
    exact ⟨isMultiplicative_one, fun q hq => by simp [one_apply, hq.one_lt.ne']⟩
  · intro n
    rw [M2L2.famI_apply, sum_singleton, one_mul, mul_one]
    congr 2
    rw [← ell_eq_zeta (k := 0) (1 : DirichletCharacter ℤ 1)]
    intro q hq; rw [M2L2.ell_trivial_apply 0 hq.ne_zero]; simp

/-! ## (B') Relaxed reading (twist condition only at primes q != 3): F9 is inside. -/

def DType3' (G : ArithmeticFunction ℤ) : Prop :=
  ∃ (N1 N2 N3 k1 k2 k3 : ℕ) (χ1 : DirichletCharacter ℤ N1) (χ2 : DirichletCharacter ℤ N2)
    (χ3 : DirichletCharacter ℤ N3),
    (∀ q : ℕ, q.Prime → q ≠ 3 → M2L2.ell χ1 k1 q ≡ 1 [ZMOD 3]) ∧
    (∀ q : ℕ, q.Prime → q ≠ 3 → M2L2.ell χ2 k2 q ≡ 1 [ZMOD 3]) ∧
    (∀ q : ℕ, q.Prime → q ≠ 3 → M2L2.ell χ3 k3 q ≡ 1 [ZMOD 3]) ∧
    G = M2L2.ell χ1 k1 * M2L2.ell χ2 k2 * M2L2.ell χ3 k3

def ConjClass' (f : ℕ → ℤ) : Prop :=
  ∃ (ι : Type) (I : Finset ι) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ),
    (∀ i ∈ I, DType3' (G i)) ∧ (∀ i ∈ I, (h i).IsMultiplicative ∧ ∀ q, q.Prime → h i q = 0) ∧
    ∀ n, f n = M2L2.famI I c G h n

lemma sq_mod3 {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3) (k : ℕ) : ((q : ℤ) ^ (2 * k)) ≡ 1 [ZMOD 3] := by
  have hnd : ¬ (3 : ℤ) ∣ q := by
    intro h
    have : (3 : ℕ) ∣ q := by exact_mod_cast h
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 this).symm
  have : (q : ℤ) % 3 = 1 ∨ (q : ℤ) % 3 = 2 := by omega
  rw [pow_mul]
  have h2 : (q : ℤ) ^ 2 ≡ 1 [ZMOD 3] := by
    rcases this with h | h
    · have := (Int.ModEq.pow 2 (show (q : ℤ) ≡ 1 [ZMOD 3] from h)); simpa using this
    · have := (Int.ModEq.pow 2 (show (q : ℤ) ≡ 2 [ZMOD 3] from h)); exact this.trans (by decide)
  simpa using h2.pow k

lemma ellOne_eq (k : ℕ) : M2L3.ellOne k = M2L2.ell (1 : DirichletCharacter ℤ 1) k := by
  ext n
  by_cases hn : n = 0
  · subst hn; simp
  · rw [M2L3.ellOne_apply, if_neg hn, M2L2.ell_trivial_apply k hn]

lemma ellPrin_eq (k : ℕ) : M2L3.ellPrin 3 k = M2L2.ell (1 : DirichletCharacter ℤ 3) k := by
  ext n
  by_cases hn : n = 0
  · subst hn; simp [M2L3.ellPrin, M2L2.ell_apply']
  · rw [M2L2.ell_apply _ k hn]
    simp only [M2L3.ellPrin, coe_mk, hn, false_or]
    by_cases h3 : 3 ∣ n
    · rw [if_pos h3]
      have : ¬ IsUnit ((n : ℕ) : ZMod 3) := by
        rw [(ZMod.natCast_eq_zero_iff n 3).2 h3]; exact not_isUnit_zero
      rw [MulChar.map_nonunit _ this, zero_mul]
    · rw [if_neg h3]
      have : IsUnit ((n : ℕ) : ZMod 3) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
      rw [MulChar.one_apply this, one_mul]

lemma prin_val {q k : ℕ} (hq : q.Prime) (h3 : q ≠ 3) :
    M2L2.ell (1 : DirichletCharacter ℤ 3) k q = (q : ℤ) ^ k := by
  rw [← ellPrin_eq, M2L3.ellPrin_apply, if_neg]
  rintro (h | h)
  · exact hq.ne_zero h
  · exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h).symm

theorem F9_in_relaxed : ConjClass' M2L3.F9 := by
  obtain ⟨hA, hB, eA, eB, mA, mB, h0, -, -⟩ := M2L3.thmD_model_mod9
  refine ⟨Bool, {true, false}, fun b => if b then 3 else -2,
    fun b => if b then M2L3.GA9 else M2L3.GB9, fun b => if b then hA else hB, ?_, ?_, ?_⟩
  · intro b _
    cases b
    · refine ⟨3, 3, 3, 0, 2, 4, 1, 1, 1, ?_, ?_, ?_, ?_⟩
      · intro q hq h3; rw [prin_val hq h3]; simpa using sq_mod3 hq h3 0
      · intro q hq h3; rw [prin_val hq h3]; simpa using sq_mod3 hq h3 1
      · intro q hq h3; rw [prin_val hq h3]; simpa using sq_mod3 hq h3 2
      · simp only [Bool.false_eq_true, if_false, M2L3.GB9, ellPrin_eq]
    · refine ⟨1, 1, 1, 0, 2, 4, 1, 1, 1, ?_, ?_, ?_, ?_⟩
      · intro q hq _; rw [M2L2.ell_trivial_apply _ hq.ne_zero]; simp
      · intro q hq h3; rw [M2L2.ell_trivial_apply _ hq.ne_zero]; simpa using sq_mod3 hq h3 1
      · intro q hq h3; rw [M2L2.ell_trivial_apply _ hq.ne_zero]; simpa using sq_mod3 hq h3 2
      · simp only [if_true, M2L3.GA9, ellOne_eq]
  · intro b _
    cases b
    · exact ⟨mB, fun q hq => (h0 q hq).2⟩
    · exact ⟨mA, fun q hq => (h0 q hq).1⟩
  · intro n
    rw [M2L2.famI_apply, sum_pair (by decide)]
    simp only [if_true, Bool.false_eq_true, if_false, eA, eB, M2L3.F9, M2L3.Ffun]
    push_cast; ring

/-! ## (C) Window check / fast path: how many blocks take the certified fast path (eval only). -/

def fastCount (y : ℕ) : ℕ × ℕ := Id.run do
  let r := Nat.sqrt y
  let mut n0 := max 1 (min (M2L5.icbrtF y + 1) (r + 1))
  let mut fast := 0
  let mut tot := 0
  for _ in [0:r+1] do
    if r < n0 then break
    let R := r + 1 - n0
    let Q := M2L5.icbrtF (n0 ^ 3 / y)
    let aq := M2L5.approx y (n0 * n0) Q
    let a := aq.1
    let q := aq.2
    tot := tot + 1
    if q = 0 ∨ Q < q ∨ R < q then
      n0 := n0 + R
    else
      let k := min Q R / q
      let H := k * q
      let ainv : ℤ := Nat.gcdA a q
      let D : ℤ := (q : ℤ) * y - (a : ℤ) * (n0 : ℤ) ^ 2
      if |D| * ((H : ℤ) - 1) < (n0 : ℤ) ^ 2 ∧ (q : ℤ) * y * ((H : ℤ) - 1) ^ 2 ≤ (n0 : ℤ) ^ 3 ∧
          ((a : ℤ) * ainv) % (q : ℤ) = 1 % (q : ℤ) then fast := fast + 1
      n0 := n0 + H
  return (fast, tot)

#eval fastCount 1000000000
#eval fastCount 123456789012

end Audit5

#print axioms Audit5.DType3_iff_d3
#print axioms Audit5.d3_in_ConjClass
#print axioms Audit5.F9_in_relaxed
