module

public import M2ResultM
public import M2AxisSwap
public import M2ConstructO
public import M2Tables
public import M2ThetaJ2
public import M2ResultN
public import M2TheoremL
public import M2Frobenius

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.omega

namespace M2L4Audit
open M2L3 M2L4 M2L2

/-! Oracle hypotheses are satisfiable by the true oracles (non-vacuity). -/
example (x : ℕ) : piMod3OfD3 (fun y => D3 y % 9) x = (Nat.primeCounting x : ZMod 3) :=
  piMod3OfD3_correct _ x (fun _ _ => rfl)
example (x : ℕ) : D3mod9OfPi (fun y => (Nat.primeCounting y : ZMod 3)) x = D3 x % 9 :=
  D3mod9OfPi_correct _ x (fun _ _ => rfl)

/-! iroot anchors. -/
example : iroot 2 10 = 3 := by decide
example : iroot 3 27 = 3 := by decide
example : iroot 3 26 = 2 := by decide

/-! The axis swap with the TRUE integer difference M - r fails at y = 1, a = 1 (c = r = 1, M = 0),
an argument that occurs in (F1) at x = 1, a = 1. So the truncated subtraction is essential. -/
example : sw_c 1 1 = 1 ∧ sw_M 1 1 = 0 := by decide
example :
    (∑ b ∈ Icc 1 (Nat.sqrt 1), ((1 / b : ℕ) : ℤ))
      ≠ ∑ b ∈ Icc 1 (sw_c 1 1), ((1 / b : ℕ) : ℤ)
        + (Nat.sqrt 1 : ℤ) * ((Nat.sqrt 1 : ℤ) - sw_c 1 1)
        + ∑ t ∈ Ioc (Nat.sqrt 1) (sw_M 1 1), ((1 / t : ℕ) : ℤ)
        - (sw_c 1 1 : ℤ) * ((sw_M 1 1 : ℤ) - Nat.sqrt 1) := by decide

/-! chi4 core values at primes: 3 + chi4(3) = 2, 5 + chi4(5) = 6, 2 + chi4(2) = 2. -/
example : core L4 3 = 2 := by
  rw [core_L4_prime Nat.prime_three]
  have : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four (by norm_num)
  push_cast at this ⊢; rw [this]; norm_num
example : core L4 5 = 6 := by
  rw [core_L4_prime (by norm_num)]
  have : ZMod.χ₄ ((5 : ℕ) : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four (by norm_num)
  push_cast at this ⊢; rw [this]; norm_num

/-! Theorem L for the actual W of (N1): (N3) holds for every x ≥ 1 given only (N2) for Wfun. -/
example (R : ℕ → Prop) [DecidablePred R] (hR : ∀ q, R q → q.Prime ∧ 3 < q ∧ q % 3 = 1)
    (hN2 : ∀ q j, q.Prime → 1 ≤ j →
      Wfun (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ (R q ∨ 3 ∣ j) then 4 else 0)
    {x : ℕ} (hx : 1 ≤ x) :
    (4 : ℤ) ∣ ∑ n ∈ Ioc 0 x, Wfun n - 1 ∧
      (piR R x : ℤ) ≡ (∑ n ∈ Ioc 0 x, Wfun n - 1) / 4 - CR R x [ZMOD 2] :=
  L_N3 Wfun hR Wfun_one (fun _ h => Wfun_eight_dvd h) hN2 hx

/-! Theorem L hypotheses are jointly consistent (toy model, R = ∅). -/
example : ∃ W : ℕ → ℤ, W 1 = 1 ∧ (∀ n, 2 ≤ ω n → 8 ∣ W n) ∧
    ∀ q j, q.Prime → 1 ≤ j →
      W (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ ((fun _ : ℕ => False) q ∨ 3 ∣ j) then 4 else 0 := by
  classical
  refine ⟨fun n => if n = 1 then 1 else if ∃ q j, q.Prime ∧ 1 ≤ j ∧ n = q ^ j ∧ 3 < q ∧ q % 3 = 1 ∧ 3 ∣ j
    then 4 else 0, by simp, fun n hn => ?_, fun q j hq hj => ?_⟩
  · have h1 : n ≠ 1 := by rintro rfl; simp at hn
    beta_reduce
    rw [ite_eq_right h1, ite_eq_right]; · exact dvd_zero _
    rintro ⟨q, j, hq, hj, rfl, -⟩
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow hq (by omega)] at hn; omega
  · have h1 : q ^ j ≠ 1 := (Nat.one_lt_pow (by omega) hq.one_lt).ne'
    simp only [ite_eq_right h1, false_or]
    congr 1
    apply propext
    constructor
    · rintro ⟨q', j', hq', hj', he, h3, h1', hd⟩
      obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hq hq' (by omega) (by omega) he
      exact ⟨h3, h1', hd⟩
    · rintro ⟨h3, h1', hd⟩; exact ⟨q, j, hq, hj, rfl, h3, h1', hd⟩

/-! rStar anchor: 28 = 1 + 27, r*(28) = 4. -/
set_option maxRecDepth 200000 in
example : rStar 28 = 4 := by decide

end M2L4Audit
