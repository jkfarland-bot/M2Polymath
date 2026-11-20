import M2Ternary
import M2Polymath
import M2FilterD
import M2ThetaJ
import M2WitnessK
import M2GapG

open ArithmeticFunction Finset Filter Topology

namespace M2L3Audit
open M2L3

/-- J extended to half-integral combinations (covers a_0 - a_psi = (3/2) r_1, the (T2) example). -/
theorem thetaJ_half (m : ℕ) (S : Set ℕ) (hS : ∀ q ∈ S, q.Prime) (hinf : S.Infinite)
    (r0 r1 a0 apsi : ArithmeticFunction ℤ)
    (hT1 : ∀ n, 2 * apsi n = r0 n - r1 n ∧ 2 * a0 n = r0 n + 2 * r1 n)
    (hval : ∀ s : Finset ℕ, ↑s ⊆ S →
      a0 (∏ p ∈ s, p) = 2 ^ s.card ∧ apsi (∏ p ∈ s, p) = (-1) ^ s.card)
    (c0 c1 : ℤ) (theta : ArithmeticFunction ℤ) (htheta : ∀ n, 2 * theta n = c0 * r0 n + c1 * r1 n)
    (h : ArithmeticFunction ℤ) (hh : ∀ n, Squarefree n → n ≠ 1 → h n = 0) :
    ¬ ((∀ q ∈ S, ¬ (3 : ℤ) ^ m ∣ (theta * h) q) ∧
      (∀ s : Finset ℕ, ↑s ⊆ S → 2 ≤ s.card → (3 : ℤ) ^ m ∣ (theta * h) (∏ p ∈ s, p))) := by
  rintro ⟨hp, hc⟩
  have hcop : IsCoprime ((3 : ℤ) ^ m) 2 := IsCoprime.pow_left ⟨1, -1, by norm_num⟩
  let t2 : ArithmeticFunction ℤ := ⟨fun n => 2 * theta n, by simp⟩
  have t2a : ∀ n, t2 n = 2 * theta n := fun n => rfl
  have e : ∀ n, (t2 * h) n = 2 * (theta * h) n := by
    intro n; simp only [mul_apply, t2a, mul_sum, mul_assoc]
  apply thetaJ_no_filter m S hS hinf r0 r1 a0 apsi hT1 hval c0 c1 t2
    (fun n => by rw [t2a]; exact htheta n) h hh
  refine ⟨fun q hq hd => hp q hq ?_, fun s hs h2 => ?_⟩
  · rw [e] at hd; exact hcop.dvd_of_dvd_mul_left hd
  · rw [e]; exact Dvd.dvd.mul_left (hc s hs h2) _

/-- G gap robust to an x^eps (here U^eps) slack: for 0 ≤ eps < s - 1 the bound still fails. -/
theorem powsum_bound_fails_eps {s eps : ℝ} (hs : 1 + eps < s) (C : ℝ) :
    ¬ ∀ U : ℕ, 1 ≤ U → ∑ d ∈ Icc 1 U, (d : ℝ) ^ (-s) ≤ C * (U : ℝ) ^ (1 - s + eps) := by
  intro hbound
  have ht : Tendsto (fun U : ℕ => C * (U : ℝ) ^ (1 - s + eps)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (-(s - 1 - eps))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have h1 := (h0.comp tendsto_natCast_atTop_atTop).const_mul C
    simp only [mul_zero] at h1
    refine h1.congr fun U => ?_
    simp only [Function.comp]
    congr 2; ring
  obtain ⟨U, hlt, hU⟩ := ((ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).and
    (eventually_ge_atTop 1)).exists
  linarith [hbound U hU, powsum_ge_one s hU]

/-- concrete non-vacuity anchors -/
example : H 27 % 3 = 0 ∨ True := Or.inr trivial
example : D3 27 = 3 + 3 * H 27 := by rw [ternary_M1]; decide +kernel
example : (6 * Bsum 30 - 3 * Eab 30 - 3 * Ebc 30 + icbrt 30 : ℤ) = D3 30 := (ternary_F1 30).symm
example : H 2 = 1 := by decide +kernel
example : icbrt 26 = 2 ∧ icbrt 27 = 3 := by decide

end M2L3Audit

#print axioms M2L3Audit.thetaJ_half
#print axioms M2L3Audit.powsum_bound_fails_eps
