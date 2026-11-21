module

public import Mathlib
public import M2BlockS
import all M2BlockS

/-!
  Seat M2L6c: the cost side of the x^(5/9) algorithm, targets 1 to 4 (PROOF_D3_5_9.md Lemmas 2, 3, 6, 7, Key Lemma).
-/

@[expose] public section

namespace M2L6c

open M2L5

/-! ## Lemma 2 for `approxAux`: the Euclid state invariant -/

/-- Invariant of a state `(u, v, p0, q0, p1, q1, best)` of `approxAux` run on `(U, V)` after at least
one step: `(U, V)` is recovered from the current remainders by the convergent matrix, the matrix has
determinant `±1`, `best` is the current convergent, its denominator lies in `[1, Q]`, and `v < u`. -/
def Inv (U V Q u v p0 q0 p1 q1 : ℕ) (best : ℕ × ℕ) : Prop :=
  U = p1 * u + p0 * v ∧ V = q1 * u + q0 * v ∧
  (p1 * q0 = p0 * q1 + 1 ∨ p0 * q1 = p1 * q0 + 1) ∧
  best = (p1, q1) ∧ 1 ≤ q1 ∧ q1 ≤ Q ∧ v < u

/-- The conclusion of PROOF Lemma 2 for `(a, q) = b`: `1 ≤ q ≤ Q`, `|q U - a V| * Q < V`
(that is `|U/V - a/q| < 1/(q Q)`, the case of error 0 included), and `gcd(a, q) = 1`. -/
def Good (U V Q : ℕ) (b : ℕ × ℕ) : Prop :=
  1 ≤ b.2 ∧ b.2 ≤ Q ∧ |(b.2 : ℤ) * U - (b.1 : ℤ) * V| * Q < V ∧ Nat.Coprime b.1 b.2

lemma good_exit {U V Q u v p0 q0 p1 q1 : ℕ} {best : ℕ × ℕ}
    (h : Inv U V Q u v p0 q0 p1 q1 best) (hex : v = 0 ∨ Q < u / v * q1 + q0) :
    Good U V Q best := by
  obtain ⟨hU, hV, hdet, hb, hq1, hqQ, hvu⟩ := h
  subst hb
  have hD : (q1 : ℤ) * U - (p1 : ℤ) * V = ((q1 : ℤ) * p0 - (p1 : ℤ) * q0) * v := by
    rw [hU, hV]; push_cast; ring
  have habs : |(q1 : ℤ) * U - (p1 : ℤ) * V| = v := by
    rw [hD, abs_mul]
    rcases hdet with h | h
    · have : (q1 : ℤ) * p0 - (p1 : ℤ) * q0 = -1 := by
        have : ((p1 * q0 : ℕ) : ℤ) = ((p0 * q1 + 1 : ℕ) : ℤ) := by rw [h]
        push_cast at this; linarith
      rw [this]; simp
    · have : (q1 : ℤ) * p0 - (p1 : ℤ) * q0 = 1 := by
        have : ((p0 * q1 : ℕ) : ℤ) = ((p1 * q0 + 1 : ℕ) : ℤ) := by rw [h]
        push_cast at this; linarith
      rw [this]; simp
  refine ⟨hq1, hqQ, ?_, ?_⟩
  · dsimp only
    rw [habs]
    by_cases h0 : v = 0
    · subst h0
      have h1 : 1 ≤ q1 * u := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      have hV1 : 1 ≤ V := by rw [hV, Nat.mul_zero, Nat.add_zero]; exact h1
      have : (1 : ℤ) ≤ V := by exact_mod_cast hV1
      simp; omega
    · have hv : 0 < v := Nat.pos_of_ne_zero h0
      have hlt : Q < u / v * q1 + q0 := hex.resolve_left h0
      have h1 : v * Q < v * (u / v * q1 + q0) := Nat.mul_lt_mul_of_pos_left hlt hv
      have h2 : v * (u / v) ≤ u := Nat.mul_div_le u v
      have h3 : v * (u / v * q1 + q0) ≤ q1 * u + q0 * v := by
        calc v * (u / v * q1 + q0) = v * (u / v) * q1 + q0 * v := by ring
          _ ≤ u * q1 + q0 * v := by gcongr
          _ = q1 * u + q0 * v := by ring
      have : v * Q < V := by omega
      exact_mod_cast this
  · dsimp only
    rw [← Nat.isCoprime_iff_coprime]
    rcases hdet with h | h
    · refine ⟨q0, -(p0 : ℤ), ?_⟩
      have : ((p1 * q0 : ℕ) : ℤ) = ((p0 * q1 + 1 : ℕ) : ℤ) := by rw [h]
      push_cast at this; linarith
    · refine ⟨-(q0 : ℤ), p0, ?_⟩
      have : ((p0 * q1 : ℕ) : ℤ) = ((p1 * q0 + 1 : ℕ) : ℤ) := by rw [h]
      push_cast at this; linarith

lemma inv_step {U V Q u v p0 q0 p1 q1 : ℕ} {best : ℕ × ℕ}
    (h : Inv U V Q u v p0 q0 p1 q1 best) (hv : v ≠ 0) (hQ : ¬ Q < u / v * q1 + q0) :
    Inv U V Q v (u % v) p1 q1 (u / v * p1 + p0) (u / v * q1 + q0)
      (u / v * p1 + p0, u / v * q1 + q0) := by
  obtain ⟨hU, hV, hdet, hb, hq1, hqQ, hvu⟩ := h
  have hu := Nat.div_add_mod u v
  have ha : 1 ≤ u / v := Nat.div_pos hvu.le (Nat.pos_of_ne_zero hv)
  refine ⟨?_, ?_, ?_, rfl, ?_, by omega, Nat.mod_lt u (Nat.pos_of_ne_zero hv)⟩
  · rw [hU]; conv_lhs => rw [← hu]
    ring
  · rw [hV]; conv_lhs => rw [← hu]
    ring
  · rcases hdet with h | h
    · right
      calc p1 * (u / v * q1 + q0) = u / v * p1 * q1 + p1 * q0 := by ring
        _ = u / v * p1 * q1 + (p0 * q1 + 1) := by rw [h]
        _ = (u / v * p1 + p0) * q1 + 1 := by ring
    · left
      calc (u / v * p1 + p0) * q1 = u / v * p1 * q1 + p0 * q1 := by ring
        _ = u / v * p1 * q1 + (p1 * q0 + 1) := by rw [h]
        _ = p1 * (u / v * q1 + q0) + 1 := by ring
  · calc 1 ≤ q1 := hq1
      _ = 1 * q1 + 0 := by ring
      _ ≤ u / v * q1 + q0 := by gcongr; omega

lemma two_mod_lt {u v : ℕ} (hv : 0 < v) (hvu : v ≤ u) : 2 * (u % v) < u := by
  have h1 := Nat.div_add_mod u v
  have h2 : 1 ≤ u / v := Nat.div_pos hvu hv
  have h3 : v * 1 ≤ v * (u / v) := Nat.mul_le_mul_left v h2
  have h4 := Nat.mod_lt u hv
  generalize v * (u / v) = m at h1 h3
  omega

lemma log2_step {w u : ℕ} (hw : w ≠ 0) (h : 2 * w < u) : Nat.log2 w + 1 ≤ Nat.log2 u := by
  rw [Nat.le_log2 (by omega), pow_succ]
  have := Nat.log2_self_le hw
  omega

/-- **Fuel suffices.** From any invariant state, fuel `2 log2 u + 2` reaches an exit of the Euclid loop
(a zero remainder or a denominator above `Q`), and the returned pair satisfies Lemma 2. -/
theorem aux_good (U V Q : ℕ) : ∀ fuel u v p0 q0 p1 q1 (best : ℕ × ℕ),
    Inv U V Q u v p0 q0 p1 q1 best → 2 * Nat.log2 u + 2 ≤ fuel →
    Good U V Q (approxAux Q fuel u v p0 q0 p1 q1 best) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro u v p0 q0 p1 q1 best hI hf
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [approxAux]
  by_cases hv : v = 0
  · rw [ite_eq_left hv]; exact good_exit hI (Or.inl hv)
  rw [ite_eq_right hv]
  by_cases hQ : Q < u / v * q1 + q0
  · rw [ite_eq_left hQ]; exact good_exit hI (Or.inr hQ)
  rw [ite_eq_right hQ]
  have hI2 := inv_step hI hv hQ
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [approxAux]
  by_cases hw : u % v = 0
  · rw [ite_eq_left hw]; exact good_exit hI2 (Or.inl hw)
  rw [ite_eq_right hw]
  by_cases hQ2 : Q < v / (u % v) * (u / v * q1 + q0) + q1
  · rw [ite_eq_left hQ2]; exact good_exit hI2 (Or.inr hQ2)
  rw [ite_eq_right hQ2]
  refine ih g (by omega) _ _ _ _ _ _ _ (inv_step hI2 hw hQ2) ?_
  have hvu := hI.2.2.2.2.2.2
  have := log2_step hw (two_mod_lt (Nat.pos_of_ne_zero hv) hvu.le)
  omega

/-- **PROOF Lemma 2 for `approx`** (fuel `2 * Nat.log2 v + 8` suffices): for `v ≥ 1` and `Q ≥ 1`,
`(a, q) = approx u v Q` has `1 ≤ q ≤ Q`, `|q u - a v| * Q < v` and `gcd(a, q) = 1`. -/
theorem approx_good (U V Q : ℕ) (hV : 0 < V) (hQ : 1 ≤ Q) : Good U V Q (approx U V Q) := by
  unfold approx
  obtain ⟨f, hf⟩ : ∃ f, 2 * Nat.log2 V + 8 = f + 1 := ⟨2 * Nat.log2 V + 7, by omega⟩
  rw [hf, approxAux, ite_eq_right (by omega), ite_eq_right (by simp; omega)]
  refine aux_good U V Q f _ _ _ _ _ _ _ ?_ (by omega)
  refine ⟨?_, ?_, ?_, rfl, by simp, by simp; omega, Nat.mod_lt U hV⟩
  · have := Nat.div_add_mod U V; simp only [mul_one, add_zero, one_mul]; linarith
  · simp
  · right; simp

theorem approx_q_pos (U V Q : ℕ) (hV : 0 < V) (hQ : 1 ≤ Q) : 1 ≤ (approx U V Q).2 :=
  (approx_good U V Q hV hQ).1

theorem approx_q_le (U V Q : ℕ) (hV : 0 < V) (hQ : 1 ≤ Q) : (approx U V Q).2 ≤ Q :=
  (approx_good U V Q hV hQ).2.1

theorem approx_err (U V Q : ℕ) (hV : 0 < V) (hQ : 1 ≤ Q) :
    |((approx U V Q).2 : ℤ) * U - ((approx U V Q).1 : ℤ) * V| * Q < V :=
  (approx_good U V Q hV hQ).2.2.1

theorem approx_coprime (U V Q : ℕ) (hV : 0 < V) (hQ : 1 ≤ Q) :
    Nat.Coprime (approx U V Q).1 (approx U V Q).2 :=
  (approx_good U V Q hV hQ).2.2.2

/-- `Nat.gcdA a q` is an inverse of `a` modulo `q` when `gcd(a, q) = 1`. -/
theorem gcdA_inv {a q : ℕ} (h : Nat.Coprime a q) :
    ((a : ℤ) * Nat.gcdA a q) % (q : ℤ) = 1 % (q : ℤ) := by
  have e := Nat.gcd_eq_gcd_ab a q
  rw [Nat.Coprime.gcd_eq_one h] at e
  have : (a : ℤ) * Nat.gcdA a q = 1 + (q : ℤ) * (-Nat.gcdB a q) := by push_cast at e; linarith
  rw [this, Int.add_mul_emod_self_left]

theorem approx_inv (U V Q : ℕ) (hV : 0 < V) (hQ : 1 ≤ Q) :
    (((approx U V Q).1 : ℤ) * Nat.gcdA (approx U V Q).1 (approx U V Q).2) % ((approx U V Q).2 : ℤ)
      = 1 % ((approx U V Q).2 : ℤ) :=
  gcdA_inv (approx_coprime U V Q hV hQ)

/-! ## The routine's setup: `Q ≥ 1` and `Q^3 y ≤ n0^3` (PROOF Lemma 3) -/

/-- `icbrt y < n0` is the routine's `n0 > c0`; it is equivalent to `y < n0 ^ 3`. -/
theorem lt_cube_iff (y n0 : ℕ) : M2L3.icbrt y < n0 ↔ y < n0 ^ 3 := by
  rw [← not_le, ← not_le, M2L3.cube_le_iff]

theorem Q_pos {y n0 : ℕ} (hy : 1 ≤ y) (hn : y < n0 ^ 3) : 1 ≤ icbrtF (n0 ^ 3 / y) := by
  rw [icbrtF_eq]
  exact M2L3.le_icbrt (by simp; exact (Nat.one_le_div_iff (by omega)).2 hn.le)

theorem Q_cube {y n0 : ℕ} : icbrtF (n0 ^ 3 / y) ^ 3 * y ≤ n0 ^ 3 := by
  rw [icbrtF_eq]
  exact (Nat.mul_le_mul_right y (M2L3.icbrt_pow_le _)).trans (Nat.div_mul_le_self _ _)

/-! ## Target 1: the fast path is always taken -/

/-- **The run-time checks of `blockStep` always pass** (PROOF Lemmas 2 and 3). Under the routine's setup
`1 ≤ y`, `y < n0 ^ 3` (that is `n0 > icbrt y`), with `Q = icbrtF (n0 ^ 3 / y)` and
`(a, q) = approx y (n0 * n0) Q`: `1 ≤ Q`, `1 ≤ q ≤ Q`, and whenever `q ≤ R = r + 1 - n0`, for
`k = min Q R / q`, `H = k q`, `D = q y - a n0 ^ 2`, the three checks of `blockStep` hold. -/
theorem blockStep_checks (y r n0 : ℕ) (hy : 1 ≤ y) (hn : y < n0 ^ 3) :
    let Q := icbrtF (n0 ^ 3 / y)
    let a := (approx y (n0 * n0) Q).1
    let q := (approx y (n0 * n0) Q).2
    let R := r + 1 - n0
    1 ≤ Q ∧ 1 ≤ q ∧ q ≤ Q ∧
    (q ≤ R →
      let H := min Q R / q * q
      let D : ℤ := (q : ℤ) * y - (a : ℤ) * (n0 : ℤ) ^ 2
      |D| * ((H : ℤ) - 1) < (n0 : ℤ) ^ 2 ∧ (q : ℤ) * y * ((H : ℤ) - 1) ^ 2 ≤ (n0 : ℤ) ^ 3 ∧
        ((a : ℤ) * Nat.gcdA a q) % (q : ℤ) = 1 % (q : ℤ)) := by
  intro Q a q R
  have hn0 : 0 < n0 := by
    rcases Nat.eq_zero_or_pos n0 with h | h
    · subst h; simp at hn
    · exact h
  have hQ : 1 ≤ Q := Q_pos hy hn
  have hV : 0 < n0 * n0 := Nat.mul_pos hn0 hn0
  obtain ⟨g1, g2, g3, g4⟩ := approx_good y (n0 * n0) Q hV hQ
  refine ⟨hQ, g1, g2, fun hqR => ?_⟩
  intro H D
  have hk : 1 ≤ min Q R / q := by rw [Nat.le_div_iff_mul_le (by omega)]; omega
  have hH1 : q ≤ H := by
    calc q = 1 * q := by ring
      _ ≤ min Q R / q * q := Nat.mul_le_mul_right q hk
  have hHQ : H ≤ Q := (Nat.div_mul_le_self _ _).trans (min_le_left _ _)
  have hH1' : (1 : ℤ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
  have hHQ' : (H : ℤ) ≤ Q := by exact_mod_cast hHQ
  have hHz1 : (0 : ℤ) ≤ (H : ℤ) - 1 := by linarith
  have hHz2 : (H : ℤ) - 1 ≤ Q := by linarith
  refine ⟨?_, ?_, gcdA_inv g4⟩
  · have e : |D| * (Q : ℤ) < (n0 : ℤ) ^ 2 := by
      have := g3; push_cast at this
      simpa [D, sq] using this
    calc |D| * ((H : ℤ) - 1) ≤ |D| * Q := mul_le_mul_of_nonneg_left hHz2 (abs_nonneg _)
      _ < _ := e
  · have e1 : ((Q ^ 3 * y : ℕ) : ℤ) ≤ ((n0 ^ 3 : ℕ) : ℤ) := by exact_mod_cast Q_cube
    push_cast at e1
    have hq : (q : ℤ) ≤ Q := by exact_mod_cast g2
    have hq0 : (0 : ℤ) ≤ q := by positivity
    have hy0 : (0 : ℤ) ≤ y := by positivity
    have e2 : ((H : ℤ) - 1) ^ 2 ≤ (Q : ℤ) ^ 2 := pow_le_pow_left₀ hHz1 hHz2 2
    calc (q : ℤ) * y * ((H : ℤ) - 1) ^ 2 ≤ (Q : ℤ) * y * (Q : ℤ) ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hq hy0) e2 (by positivity) (by positivity)
      _ = (Q : ℤ) ^ 3 * y := by ring
      _ ≤ _ := e1

/-- **Target 1: `blockStep` returns `blockFast` whenever it does not take the `R < q` branch.**
Under the routine's setup `1 ≤ y`, `y < n0 ^ 3` (that is `n0 > icbrt y`, `lt_cube_iff`), for any `r`:
if `q ≤ R = r + 1 - n0` then `blockStep y r n0 = (k q, blockFast y n0 a q (gcdA a q) k)` with
`Q = icbrtF (n0 ^ 3 / y)`, `(a, q) = approx y (n0 * n0) Q`, `k = min Q R / q`. -/
theorem blockStep_fast (y r n0 : ℕ) (hy : 1 ≤ y) (hn : y < n0 ^ 3)
    (hR : (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2 ≤ r + 1 - n0) :
    blockStep y r n0 =
      (min (icbrtF (n0 ^ 3 / y)) (r + 1 - n0) / (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2
          * (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2,
        blockFast y n0 (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).1
          (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2
          (Nat.gcdA (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).1
            (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2)
          (min (icbrtF (n0 ^ 3 / y)) (r + 1 - n0) / (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2)) := by
  obtain ⟨hQ, hq1, hqQ, hchk⟩ := blockStep_checks y r n0 hy hn
  have hc := hchk hR
  unfold blockStep
  dsimp only at hc hQ hq1 hqQ hR ⊢
  rw [ite_eq_right (by omega), ite_eq_left hc]

/-- The other branch: if `R < q` the block is the rest of the range, summed directly. -/
theorem blockStep_tail (y r n0 : ℕ)
    (hR : r + 1 - n0 < (approx y (n0 * n0) (icbrtF (n0 ^ 3 / y))).2) :
    blockStep y r n0 = (r + 1 - n0, direct y n0 (r + 1 - n0)) := by
  unfold blockStep
  dsimp only at hR ⊢
  rw [ite_eq_left (Or.inr (Or.inr hR))]

/-- In the tail branch the direct sum is short: fewer than `q ≤ Q ≤ y^(1/6)` terms (`Q ^ 6 ≤ y` when
`n0 ≤ isqrt y`). -/
theorem tail_short {y n0 : ℕ} (hy : 1 ≤ y) (hr : n0 ≤ Nat.sqrt y) :
    icbrtF (n0 ^ 3 / y) ^ 6 ≤ y := by
  have h1 := @Q_cube y n0
  have h2 : n0 * n0 ≤ y := Nat.le_sqrt.1 hr
  have h3 : n0 ^ 6 ≤ y ^ 3 := by
    calc n0 ^ 6 = (n0 * n0) ^ 3 := by ring
      _ ≤ y ^ 3 := Nat.pow_le_pow_left h2 3
  set Q := icbrtF (n0 ^ 3 / y)
  have h4 : (Q ^ 3 * y) ^ 2 ≤ (n0 ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
  have h5 : Q ^ 6 * y ^ 2 ≤ y ^ 3 := by
    calc Q ^ 6 * y ^ 2 = (Q ^ 3 * y) ^ 2 := by ring
      _ ≤ (n0 ^ 3) ^ 2 := h4
      _ = n0 ^ 6 := by ring
      _ ≤ y ^ 3 := h3
  have hy2 : 0 < y ^ 2 := by positivity
  have : Q ^ 6 * y ^ 2 ≤ y * y ^ 2 := by
    calc Q ^ 6 * y ^ 2 ≤ y ^ 3 := h5
      _ = y * y ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right this hy2


/-- The number of calls of `blockStep` made by `loop y r fuel n0` (same recursion as `loop`). -/
def nblocks (y r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n0 => if r < n0 then 0 else 1 + nblocks y r fuel (n0 + (blockStep y r n0).1)

/-- **Progress of one block** (PROOF Lemma 7 (b), (d)). For `n0 ≤ r`, `R = r + 1 - n0` and any `c`
with `y < c ^ 3`, the block length `H` satisfies `R + 1 ≤ 2 H` or `n0 + 1 ≤ 2 c H`. -/
theorem blockStep_progress (y r n0 c : ℕ) (hc : y < c ^ 3) (h2 : n0 ≤ r) :
    r + 1 - n0 + 1 ≤ 2 * (blockStep y r n0).1 ∨ n0 + 1 ≤ 2 * c * (blockStep y r n0).1 := by
  unfold blockStep
  dsimp only
  set Q := icbrtF (n0 ^ 3 / y) with hQdef
  set q := (approx y (n0 * n0) Q).2
  split_ifs with hA hB
  · left; dsimp only; omega
  all_goals
    push Not at hA
    obtain ⟨hq0, hqQ, hqR⟩ := hA
    dsimp only
    set m := min Q (r + 1 - n0) with hm
    have hk : 1 ≤ m / q := by rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have hdm := Nat.div_add_mod m q
    have hmod := Nat.mod_lt m (show 0 < q by omega)
    have hqH : q ≤ m / q * q := by
      calc q = 1 * q := by ring
        _ ≤ m / q * q := Nat.mul_le_mul_right q hk
    have h2H : m + 1 ≤ 2 * (m / q * q) := by
      have : m = m / q * q + m % q := by rw [mul_comm]; omega
      omega
    by_cases hRQ : r + 1 - n0 ≤ Q
    · left
      have : m = r + 1 - n0 := min_eq_right hRQ
      omega
    · right
      have hmQ : m = Q := min_eq_left (by omega)
      have hy : 1 ≤ y := by
        rcases Nat.eq_zero_or_pos y with h | h
        · exfalso
          have : Q = 0 := by rw [hQdef, h, Nat.div_zero, icbrtF_eq]; exact Nat.le_zero.1 (M2L3.icbrt_le 0)
          omega
        · exact h
      -- n0 < (Q + 1) c
      have e1 : ¬ (Q + 1) ^ 3 ≤ n0 ^ 3 / y := by
        rw [M2L3.cube_le_iff, ← icbrtF_eq, ← hQdef]; omega
      have e2 : n0 ^ 3 < (Q + 1) ^ 3 * y := by
        have := Nat.lt_mul_div_succ (n0 ^ 3) (show 0 < y by omega)
        have h3 : n0 ^ 3 / y + 1 ≤ (Q + 1) ^ 3 := by omega
        calc n0 ^ 3 < y * (n0 ^ 3 / y + 1) := this
          _ ≤ y * (Q + 1) ^ 3 := Nat.mul_le_mul_left y h3
          _ = (Q + 1) ^ 3 * y := by ring
      have e3 : (Q + 1) ^ 3 * y < (Q + 1) ^ 3 * c ^ 3 :=
        Nat.mul_lt_mul_of_pos_left hc (by positivity)
      have e4 : n0 ^ 3 < ((Q + 1) * c) ^ 3 := by rw [mul_pow]; omega
      have e5 : n0 < (Q + 1) * c := (Nat.pow_lt_pow_iff_left (by norm_num)).1 e4
      have e6 : (Q + 1) * c ≤ 2 * (m / q * q) * c := Nat.mul_le_mul_right c (by omega)
      calc n0 + 1 ≤ (Q + 1) * c := e5
        _ ≤ 2 * (m / q * q) * c := e6
        _ = 2 * c * (m / q * q) := by ring

/-- The potential of PROOF Lemma 7: `(2c + 1) ln((r + 1)/n0) + log2(R + 1)`, `R = r + 1 - n0`. -/
noncomputable def pot (r c n0 : ℕ) : ℝ :=
  (2 * c + 1) * (Real.log (r + 1) - Real.log n0) + Real.logb 2 (((r + 1 - n0 : ℕ) : ℝ) + 1)

lemma pot_nonneg {r c n0 : ℕ} (h1 : 1 ≤ n0) (h2 : n0 ≤ r + 1) : 0 ≤ pot r c n0 := by
  unfold pot
  have a1 : Real.log n0 ≤ Real.log (r + 1) := by
    apply Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)
  have a2 : 0 ≤ Real.logb 2 (((r + 1 - n0 : ℕ) : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith [(by positivity : (0 : ℝ) ≤ ((r + 1 - n0 : ℕ) : ℝ))])
  have : (0 : ℝ) ≤ 2 * c + 1 := by positivity
  nlinarith

/-- One block lowers the potential by at least 1. -/
lemma pot_step {y r c n0 : ℕ} (hc : y < c ^ 3) (h1 : 1 ≤ n0) (h2 : n0 ≤ r) :
    pot r c (n0 + (blockStep y r n0).1) + 1 ≤ pot r c n0 := by
  obtain ⟨s1, s2, -⟩ := blockStep_spec y r n0 h1 h2
  have hprog := blockStep_progress y r n0 c hc h2
  set H := (blockStep y r n0).1
  unfold pot
  have hR : r + 1 - (n0 + H) ≤ r + 1 - n0 := by omega
  have hRr : (((r + 1 - (n0 + H) : ℕ) : ℝ) + 1) ≤ ((r + 1 - n0 : ℕ) : ℝ) + 1 := by
    have : ((r + 1 - (n0 + H) : ℕ) : ℝ) ≤ ((r + 1 - n0 : ℕ) : ℝ) := by exact_mod_cast hR
    linarith
  have hpos : (0 : ℝ) < ((r + 1 - (n0 + H) : ℕ) : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) < n0 := by exact_mod_cast h1
  have hn0' : (0 : ℝ) < ((n0 + H : ℕ) : ℝ) := by positivity
  have hlogmono : Real.log n0 ≤ Real.log ((n0 + H : ℕ) : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast (show n0 ≤ n0 + H by omega))
  have hc0 : (0 : ℝ) ≤ 2 * c + 1 := by positivity
  rcases hprog with hp | hp
  · -- R halves
    have hb : Real.logb 2 (((r + 1 - (n0 + H) : ℕ) : ℝ) + 1) + 1
        ≤ Real.logb 2 (((r + 1 - n0 : ℕ) : ℝ) + 1) := by
      have e1 : 2 * (((r + 1 - (n0 + H) : ℕ) : ℝ) + 1) ≤ ((r + 1 - n0 : ℕ) : ℝ) + 1 := by
        have : 2 * (r + 1 - (n0 + H) + 1) ≤ r + 1 - n0 + 1 := by omega
        exact_mod_cast this
      have e2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) e1
      rw [Real.logb_mul (by norm_num) hpos.ne', Real.logb_self_eq_one (by norm_num)] at e2
      linarith
    have : (2 * c + 1) * (Real.log (r + 1) - Real.log ((n0 + H : ℕ) : ℝ))
        ≤ (2 * c + 1) * (Real.log (r + 1) - Real.log n0) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    linarith
  · -- n0 grows by the factor 1 + 1/(2c)
    have hb : Real.logb 2 (((r + 1 - (n0 + H) : ℕ) : ℝ) + 1)
        ≤ Real.logb 2 (((r + 1 - n0 : ℕ) : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hpos hRr
    have hl : 1 ≤ (2 * c + 1) * (Real.log ((n0 + H : ℕ) : ℝ) - Real.log n0) := by
      rw [← Real.log_div hn0'.ne' hn0.ne']
      have e1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0' hn0)
      rw [inv_div] at e1
      have key : (1 : ℝ) - (n0 : ℝ) / ((n0 + H : ℕ) : ℝ) = (H : ℝ) / ((n0 + H : ℕ) : ℝ) := by
        rw [eq_div_iff hn0'.ne', sub_mul, div_mul_cancel₀ _ hn0'.ne']; push_cast; ring
      have e2 : 1 ≤ (2 * c + 1) * (1 - (n0 : ℝ) / ((n0 + H : ℕ) : ℝ)) := by
        rw [key, mul_div_assoc', le_div_iff₀ hn0']
        have : n0 ≤ 2 * c * H := by omega
        have : ((n0 : ℕ) : ℝ) ≤ 2 * c * H := by exact_mod_cast this
        push_cast
        linarith
      nlinarith
    linarith

/-- **Target 2, block count with logarithms** (PROOF Lemma 7 with `4c` replaced by `2c`): for any `c`
with `y < c ^ 3` (for example `c = icbrt y + 1`), any fuel and `1 ≤ n0 ≤ r + 1`,
`#blocks ≤ 1 + (2c + 1) ln((r + 1)/n0) + log2(r + 2 - n0)`. -/
theorem nblocks_le_pot (y r c : ℕ) (hc : y < c ^ 3) : ∀ fuel n0, 1 ≤ n0 → n0 ≤ r + 1 →
    (nblocks y r fuel n0 : ℝ) ≤ 1 + pot r c n0 := by
  intro fuel
  induction fuel with
  | zero => intro n0 h1 h2; simp [nblocks]; linarith [pot_nonneg (c := c) h1 h2]
  | succ f ih =>
    intro n0 h1 h2
    unfold nblocks
    by_cases hr : r < n0
    · rw [ite_eq_left hr]; simp; linarith [pot_nonneg (c := c) h1 h2]
    rw [ite_eq_right hr]
    obtain ⟨s1, s2, -⟩ := blockStep_spec y r n0 h1 (by omega)
    have := ih (n0 + (blockStep y r n0).1) (by omega) s2
    have := pot_step (r := r) (c := c) hc h1 (by omega)
    push_cast
    linarith

lemma log_le_logb_two {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.logb 2 x := by
  unfold Real.logb
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [le_div_iff₀ h2]
  nlinarith

lemma logb_two_lt_natLog (n : ℕ) (hn : 1 ≤ n) : Real.logb 2 n < Nat.log 2 n + 1 := by
  have e := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have e' : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast e
  have := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hn) e'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
  push_cast at this; linarith

/-- **Target 2, natural-number form.** For every `y ≥ 1` and every start `1 ≤ n0 ≤ isqrt y + 1`, with
any fuel, the loop on `[n0, isqrt y]` makes at most `4 (icbrt y + 1) (Nat.log 2 y + 2) + 1` blocks. -/
theorem nblocks_le (y fuel n0 : ℕ) (hy : 1 ≤ y) (h1 : 1 ≤ n0) (h2 : n0 ≤ Nat.sqrt y + 1) :
    nblocks y (Nat.sqrt y) fuel n0 ≤ 4 * (M2L3.icbrt y + 1) * (Nat.log 2 y + 2) + 1 := by
  set r := Nat.sqrt y
  set c := M2L3.icbrt y + 1
  have hc : y < c ^ 3 := by
    by_contra h; push Not at h
    have := M2L3.le_icbrt h; omega
  have hp := nblocks_le_pot y r c hc fuel n0 h1 h2
  unfold pot at hp
  set L := Nat.log 2 (r + 1)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [(by positivity : (0 : ℝ) ≤ r)]
  have hlb : Real.logb 2 ((r : ℝ) + 1) < L + 1 := by
    have := logb_two_lt_natLog (r + 1) (by omega); push_cast at this; exact this
  have hln : Real.log ((r : ℝ) + 1) < L + 1 := (log_le_logb_two hr1).trans_lt hlb
  have hlog0 : 0 ≤ Real.log (n0 : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
  have hR : Real.logb 2 (((r + 1 - n0 : ℕ) : ℝ) + 1) ≤ Real.logb 2 ((r : ℝ) + 1) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    have : ((r + 1 - n0 : ℕ) : ℝ) ≤ r := by exact_mod_cast (show r + 1 - n0 ≤ r by omega)
    linarith
  have hc0 : (0 : ℝ) ≤ 2 * c + 1 := by positivity
  have hmain : (nblocks y r fuel n0 : ℝ) ≤ 1 + (2 * c + 2) * (L + 1) := by
    have : (2 * (c : ℝ) + 1) * (Real.log ((r : ℝ) + 1) - Real.log n0) ≤ (2 * c + 1) * (L + 1) := by
      apply mul_le_mul_of_nonneg_left _ hc0; linarith
    nlinarith
  have hL : L ≤ Nat.log 2 y + 1 := by
    have : r + 1 ≤ y * 2 := by have := Nat.sqrt_le_self y; omega
    calc L ≤ Nat.log 2 (y * 2) := Nat.log_mono_right this
      _ = Nat.log 2 y + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have hnat : nblocks y r fuel n0 ≤ 1 + (2 * c + 2) * (L + 1) := by exact_mod_cast hmain
  calc nblocks y r fuel n0 ≤ 1 + (2 * c + 2) * (L + 1) := hnat
    _ ≤ 1 + (2 * c + 2) * (Nat.log 2 y + 2) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) 1
    _ ≤ 4 * (M2L3.icbrt y + 1) * (Nat.log 2 y + 2) + 1 := by
      have : 2 * c + 2 ≤ 4 * (M2L3.icbrt y + 1) := by omega
      nlinarith

/-- The blocks of `blockSZ y L`: its call `loop y r (r + 1) n1` makes at most
`4 (icbrt y + 1) (Nat.log 2 y + 2) + 1` blocks, uniformly in `L`. -/
theorem blockSZ_nblocks (y L : ℕ) (hy : 1 ≤ y) :
    nblocks y (Nat.sqrt y) (Nat.sqrt y + 1) (max (L + 1) (min (icbrtF y + 1) (Nat.sqrt y + 1)))
      ≤ 4 * (M2L3.icbrt y + 1) * (Nat.log 2 y + 2) + 1 := by
  by_cases h : max (L + 1) (min (icbrtF y + 1) (Nat.sqrt y + 1)) ≤ Nat.sqrt y + 1
  · exact nblocks_le y _ _ hy (by omega) h
  · have : Nat.sqrt y < max (L + 1) (min (icbrtF y + 1) (Nat.sqrt y + 1)) := by omega
    rw [nblocks, ite_eq_left this]; omega


/-! ## Target 3: per-block work, as step counters proved to agree with the routine -/

lemma log_two_step {m n : ℕ} (h : 2 * m ≤ n) (hn : 1 ≤ n) : Nat.log 2 (2 * m) + 1 ≤ Nat.log 2 (2 * n) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    simp only [mul_zero, Nat.log_zero_right, zero_add]
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  · rw [← Nat.log_mul_base (by norm_num) (by omega)]
    exact Nat.log_mono_right (by omega)

/-- Binary search with an evaluation counter: `(bfirst p lo hi, number of evaluations of p)`. -/
def bfirstW (p : ℕ → Bool) (lo hi : ℕ) : ℕ × ℕ :=
  if h : lo < hi then
    if p ((lo + hi) / 2) then
      ((bfirstW p lo ((lo + hi) / 2)).1, (bfirstW p lo ((lo + hi) / 2)).2 + 1)
    else ((bfirstW p ((lo + hi) / 2 + 1) hi).1, (bfirstW p ((lo + hi) / 2 + 1) hi).2 + 1)
  else (lo, 0)
termination_by hi - lo
decreasing_by all_goals omega

theorem bfirstW_spec (p : ℕ → Bool) : ∀ (n lo hi : ℕ), hi - lo = n →
    (bfirstW p lo hi).1 = bfirst p lo hi ∧ (bfirstW p lo hi).2 ≤ Nat.log 2 (2 * (hi - lo)) ∧
    (lo ≤ hi → lo ≤ (bfirstW p lo hi).1 ∧ (bfirstW p lo hi).1 ≤ hi) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lo hi hn
  rw [bfirstW.eq_1, bfirst.eq_1]
  by_cases h1 : lo < hi
  · rw [dif_pos h1, dif_pos h1]
    by_cases h2 : p ((lo + hi) / 2) = true
    · rw [ite_eq_left h2, ite_eq_left h2]
      obtain ⟨a1, a2, a3⟩ := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
      refine ⟨a1, ?_, fun _ => ⟨(a3 (by omega)).1, by have := (a3 (by omega)).2; omega⟩⟩
      have := log_two_step (m := (lo + hi) / 2 - lo) (n := hi - lo) (by omega) (by omega)
      dsimp only; omega
    · rw [ite_eq_right h2, ite_eq_right h2]
      obtain ⟨a1, a2, a3⟩ := ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl
      refine ⟨a1, ?_, fun _ => ⟨by have := (a3 (by omega)).1; omega, (a3 (by omega)).2⟩⟩
      have := log_two_step (m := hi - ((lo + hi) / 2 + 1)) (n := hi - lo) (by omega) (by omega)
      dsimp only; omega
  · rw [dif_neg h1, dif_neg h1]
    exact ⟨rfl, by simp, fun _ => ⟨le_rfl, by omega⟩⟩

theorem bfirstW_fst (p : ℕ → Bool) (lo hi : ℕ) : (bfirstW p lo hi).1 = bfirst p lo hi :=
  (bfirstW_spec p _ lo hi rfl).1

/-- **Binary search cost**: at most `Nat.log 2 (2 (hi - lo))` evaluations (`floor(log2 (hi - lo)) + 1`). -/
theorem bfirstW_evals (p : ℕ → Bool) (lo hi : ℕ) : (bfirstW p lo hi).2 ≤ Nat.log 2 (2 * (hi - lo)) :=
  (bfirstW_spec p _ lo hi rfl).2.1

theorem bfirst_mem (p : ℕ → Bool) {lo hi : ℕ} (h : lo ≤ hi) : lo ≤ bfirst p lo hi ∧ bfirst p lo hi ≤ hi := by
  rw [← bfirstW_fst]; exact (bfirstW_spec p _ lo hi rfl).2.2 h

/-- `icbrtF` with its evaluation count. -/
def icbrtW (n : ℕ) : ℕ × ℕ :=
  ((bfirstW (fun m => decide (n < m ^ 3)) 0 (n + 1)).1 - 1, (bfirstW (fun m => decide (n < m ^ 3)) 0 (n + 1)).2)

theorem icbrtW_fst (n : ℕ) : (icbrtW n).1 = icbrtF n := by
  unfold icbrtW icbrtF; rw [bfirstW_fst]

theorem icbrtW_evals (n : ℕ) : (icbrtW n).2 ≤ Nat.log 2 (2 * (n + 1)) := by
  have := bfirstW_evals (fun m => decide (n < m ^ 3)) 0 (n + 1)
  unfold icbrtW; simpa using this

/-- `approxAux` with a counter of its division steps. -/
def approxAuxW (Q : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → (ℕ × ℕ) × ℕ
  | 0, _, _, _, _, _, _, best => (best, 0)
  | fuel + 1, u, v, p0, q0, p1, q1, best =>
    if v = 0 then (best, 1) else
    if Q < u / v * q1 + q0 then (best, 1)
    else ((approxAuxW Q fuel v (u % v) p1 q1 (u / v * p1 + p0) (u / v * q1 + q0)
        (u / v * p1 + p0, u / v * q1 + q0)).1,
      (approxAuxW Q fuel v (u % v) p1 q1 (u / v * p1 + p0) (u / v * q1 + q0)
        (u / v * p1 + p0, u / v * q1 + q0)).2 + 1)

theorem approxAuxW_fst (Q : ℕ) : ∀ fuel u v p0 q0 p1 q1 (best : ℕ × ℕ),
    (approxAuxW Q fuel u v p0 q0 p1 q1 best).1 = approxAux Q fuel u v p0 q0 p1 q1 best := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ f ih =>
    intro u v p0 q0 p1 q1 best
    rw [approxAuxW, approxAux]
    split_ifs
    · rfl
    · rfl
    · exact ih _ _ _ _ _ _ _

/-- `approx` with its step count. -/
def approxW (u v Q : ℕ) : (ℕ × ℕ) × ℕ := approxAuxW Q (2 * Nat.log2 v + 8) u v 0 1 1 0 (0, 0)

theorem approxW_fst (u v Q : ℕ) : (approxW u v Q).1 = approx u v Q := approxAuxW_fst _ _ _ _ _ _ _ _ _

theorem auxW_steps (U V Q : ℕ) : ∀ fuel u v p0 q0 p1 q1 (best : ℕ × ℕ),
    Inv U V Q u v p0 q0 p1 q1 best →
    (approxAuxW Q fuel u v p0 q0 p1 q1 best).2 ≤ 2 * (Nat.log 2 Q - Nat.log 2 q1) + 2 := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro u v p0 q0 p1 q1 best hI
  rcases fuel with _ | f
  · simp [approxAuxW]
  rw [approxAuxW]
  by_cases hv : v = 0
  · rw [ite_eq_left hv]; dsimp only; omega
  rw [ite_eq_right hv]
  by_cases hQ : Q < u / v * q1 + q0
  · rw [ite_eq_left hQ]; dsimp only; omega
  rw [ite_eq_right hQ]
  dsimp only
  have hI2 := inv_step hI hv hQ
  rcases f with _ | g
  · simp [approxAuxW]
  rw [approxAuxW]
  by_cases hw : u % v = 0
  · rw [ite_eq_left hw]; dsimp only; omega
  rw [ite_eq_right hw]
  by_cases hQ2 : Q < v / (u % v) * (u / v * q1 + q0) + q1
  · rw [ite_eq_left hQ2]; dsimp only; omega
  rw [ite_eq_right hQ2]
  dsimp only
  have hI3 := inv_step hI2 hw hQ2
  have := ih g (by omega) _ _ _ _ _ _ _ hI3
  -- the denominator at least doubles in two steps
  have hvu := hI.2.2.2.2.2.2
  have hq1 := hI.2.2.2.2.1
  have ha1 : 1 ≤ u / v := Nat.div_pos hvu.le (Nat.pos_of_ne_zero hv)
  have ha2 : 1 ≤ v / (u % v) := Nat.div_pos (Nat.mod_lt u (Nat.pos_of_ne_zero hv)).le (Nat.pos_of_ne_zero hw)
  have e1 : q1 ≤ u / v * q1 := Nat.le_mul_of_pos_left _ ha1
  have e2 : u / v * q1 + q0 ≤ v / (u % v) * (u / v * q1 + q0) := Nat.le_mul_of_pos_left _ ha2
  have hdbl : 2 * q1 ≤ v / (u % v) * (u / v * q1 + q0) + q1 := by omega
  have hle : v / (u % v) * (u / v * q1 + q0) + q1 ≤ Q := by omega
  have l1 : Nat.log 2 q1 + 1 ≤ Nat.log 2 (v / (u % v) * (u / v * q1 + q0) + q1) := by
    rw [← Nat.log_mul_base (by norm_num) (by omega)]
    exact Nat.log_mono_right (by omega)
  have l2 : Nat.log 2 (v / (u % v) * (u / v * q1 + q0) + q1) ≤ Nat.log 2 Q := Nat.log_mono_right hle
  omega

/-- **PROOF Lemma 2, step count**: `approx u v Q` makes at most `2 log2 Q + 3` division steps
(for every `u, v, Q`). -/
theorem approxW_steps (U V Q : ℕ) : (approxW U V Q).2 ≤ 2 * Nat.log 2 Q + 3 := by
  unfold approxW
  obtain ⟨f, hf⟩ : ∃ f, 2 * Nat.log2 V + 8 = f + 1 := ⟨2 * Nat.log2 V + 7, by omega⟩
  rw [hf, approxAuxW]
  by_cases hV : V = 0
  · rw [ite_eq_left hV]; dsimp only; omega
  rw [ite_eq_right hV]
  by_cases hQ : Q < U / V * 0 + 1
  · rw [ite_eq_left hQ]; dsimp only; omega
  rw [ite_eq_right hQ]
  dsimp only
  have hV' : 0 < V := Nat.pos_of_ne_zero hV
  have hI : Inv U V Q V (U % V) 1 0 (U / V * 1 + 0) (U / V * 0 + 1) (U / V * 1 + 0, U / V * 0 + 1) := by
    refine ⟨?_, ?_, ?_, rfl, by simp, by simp at hQ ⊢; omega, Nat.mod_lt U hV'⟩
    · have := Nat.div_add_mod U V; simp only [mul_one, add_zero, one_mul]; linarith
    · simp
    · right; simp
  have := auxW_steps U V Q f _ _ _ _ _ _ _ hI
  simp only [mul_zero, zero_add, mul_one, add_zero] at this ⊢
  simp only [Nat.log_one_right, Nat.sub_zero] at this
  omega

/-- `Nat.xgcdAux` (extended Euclid, used by `Nat.gcdA`) with a step counter. -/
def xgcdAuxW : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → (ℕ × ℤ × ℤ) × ℕ
  | 0, _, _, r', s', t' => ((r', s', t'), 0)
  | k + 1, s, t, r', s', t' =>
    ((xgcdAuxW (r' % (k + 1)) (s' - (r' / (k + 1) : ℕ) * s) (t' - (r' / (k + 1) : ℕ) * t) (k + 1) s t).1,
     (xgcdAuxW (r' % (k + 1)) (s' - (r' / (k + 1) : ℕ) * s) (t' - (r' / (k + 1) : ℕ) * t) (k + 1) s t).2 + 1)
termination_by k => k
decreasing_by exact Nat.mod_lt _ (by omega)

theorem xgcdAuxW_spec : ∀ n x s t r' s' t', x = n →
    (xgcdAuxW x s t r' s' t').1 = Nat.xgcdAux x s t r' s' t' ∧
    (xgcdAuxW x s t r' s' t').2 ≤ 2 * Nat.log 2 (2 * x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x s t r' s' t' hx
  rcases x with _ | k
  · rw [xgcdAuxW, Nat.xgcd_zero_left]; simp
  rw [xgcdAuxW, Nat.xgcdAux_rec (by omega : 0 < k + 1)]
  obtain ⟨b1, b2⟩ := ih (r' % (k + 1)) (by rw [← hx]; exact Nat.mod_lt _ (by omega)) _ _ _ _ _ _ rfl
  refine ⟨b1, ?_⟩
  dsimp only
  -- second step
  set w := r' % (k + 1) with hw
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · rw [h0] at b2 ⊢
    rw [xgcdAuxW]
    have := log_two_step (m := 0) (n := k + 1) (by omega) (by omega)
    simp at this ⊢; omega
  · obtain ⟨w', hw'⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rw [hw', xgcdAuxW]
    dsimp only
    have hwlt : w < k + 1 := Nat.mod_lt _ (by omega)
    have hlt : (k + 1) % (w' + 1) < n := by
      rw [← hx]; have := Nat.mod_lt (k + 1) (show 0 < w' + 1 by omega); omega
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right ((ih _ hlt _ _ _ _ _ _ rfl).2) 1) 1) ?_
    have h2 := two_mod_lt (u := k + 1) (v := w' + 1) (by omega) (by omega)
    have := log_two_step (m := (k + 1) % (w' + 1)) (n := k + 1) (by omega) (by omega)
    omega

theorem xgcdAuxW_steps' (x : ℕ) (s t : ℤ) (r' : ℕ) (s' t' : ℤ) :
    (xgcdAuxW x s t r' s' t').2 ≤ 1 + 2 * Nat.log 2 (2 * r') := by
  rcases x with _ | k
  · rw [xgcdAuxW]; omega
  rw [xgcdAuxW]
  dsimp only
  have := (xgcdAuxW_spec _ (r' % (k + 1)) (s' - (r' / (k + 1) : ℕ) * s) (t' - (r' / (k + 1) : ℕ) * t)
    (k + 1) s t rfl).2
  have : Nat.log 2 (2 * (r' % (k + 1))) ≤ Nat.log 2 (2 * r') := Nat.log_mono_right (by
    have := Nat.mod_le r' (k + 1); omega)
  omega

/-- The modular inverse `Nat.gcdA a q` with its step count. -/
def gcdAW (a q : ℕ) : ℤ × ℕ := ((xgcdAuxW a 1 0 q 0 1).1.2.1, (xgcdAuxW a 1 0 q 0 1).2)

theorem gcdAW_fst (a q : ℕ) : (gcdAW a q).1 = Nat.gcdA a q := by
  unfold gcdAW Nat.gcdA Nat.xgcd
  rw [(xgcdAuxW_spec _ a 1 0 q 0 1 rfl).1]

/-- **Modular inverse cost**: at most `1 + 2 log2 (2 q)` extended Euclid steps. -/
theorem gcdAW_steps (a q : ℕ) : (gcdAW a q).2 ≤ 1 + 2 * Nat.log 2 (2 * q) := xgcdAuxW_steps' _ _ _ _ _ _

/-- `countLe` with a count of the evaluations of `P` (PROOF Lemma 6). The argmax search evaluates `P`
twice per step, the other two searches at most once per step, plus one evaluation at the argmax. -/
def countLeW (P : ℕ → ℤ) (y : ℤ) (k : ℕ) : ℕ × ℕ :=
  if k = 0 then (0, 0) else
  let ls := bfirstW (fun l => decide (P (l + 1) - P l ≤ 0)) 0 (k - 1)
  if P ls.1 ≤ y then (k, 2 * ls.2 + 1) else
  let left := bfirstW (fun l => decide (y < P l)) 0 ls.1
  let right := bfirstW (fun l => decide (l = k ∨ P l ≤ y)) ls.1 k
  (k - (right.1 - left.1), 2 * ls.2 + 1 + left.2 + right.2)

theorem countLeW_fst (P : ℕ → ℤ) (y : ℤ) (k : ℕ) : (countLeW P y k).1 = countLe P y k := by
  unfold countLeW countLe
  simp only [bfirstW_fst]
  split_ifs <;> rfl

/-- **PROOF Lemma 6, evaluation count**: `countLe P y k` evaluates `P` at most `4 log2 (2k) + 1` times
(`4 floor(log2 k) + 5` for `k ≥ 1`), for every `P`. -/
theorem countLeW_evals (P : ℕ → ℤ) (y : ℤ) (k : ℕ) : (countLeW P y k).2 ≤ 4 * Nat.log 2 (2 * k) + 1 := by
  unfold countLeW
  by_cases hk : k = 0
  · rw [ite_eq_left hk]; omega
  rw [ite_eq_right hk]
  dsimp only
  have e1 := bfirstW_evals (fun l => decide (P (l + 1) - P l ≤ 0)) 0 (k - 1)
  have m1 := (bfirstW_spec (fun l => decide (P (l + 1) - P l ≤ 0)) _ 0 (k - 1) rfl).2.2 (by omega)
  set ls := bfirstW (fun l => decide (P (l + 1) - P l ≤ 0)) 0 (k - 1)
  have l1 : Nat.log 2 (2 * (k - 1 - 0)) ≤ Nat.log 2 (2 * k) := Nat.log_mono_right (by omega)
  split_ifs
  · omega
  · have e2 := bfirstW_evals (fun l => decide (y < P l)) 0 ls.1
    have e3 := bfirstW_evals (fun l => decide (l = k ∨ P l ≤ y)) ls.1 k
    have l2 : Nat.log 2 (2 * (ls.1 - 0)) ≤ Nat.log 2 (2 * k) := Nat.log_mono_right (by omega)
    have l3 : Nat.log 2 (2 * (k - ls.1)) ≤ Nat.log 2 (2 * k) := Nat.log_mono_right (by omega)
    dsimp only
    omega

/-! ## Target 4: an instrumented copy of `blockSZ` and its total work

Cost model (unit = one arithmetic operation or comparison on `O(log y)`-bit integers, constants generous):
each evaluation of a level polynomial `P` in `countLe` costs 8, each division step of `approx` and of the
extended Euclid of `Nat.gcdA` costs 6, each step of the bisection `icbrtF` costs 1 (it is one cube and one
comparison, charged inside the constant below), each term of `direct` costs 1, fixed overheads as written
below, and `Nat.sqrt y` is charged `2 log2 y + 2` (it is a library primitive, not instrumented). All
other counters are measured by the instrumented copies of target 3. -/

/-- `cnt3` with its cost. -/
def cnt3W (y a q m f : ℤ) (k : ℕ) : ℤ × ℕ :=
  ((countLeW (fun l => (f - a * l) * (m + q * l)) y k).1
    + (countLeW (fun l => (f + 1 - a * l) * (m + q * l)) y k).1
    + (countLeW (fun l => (f + 2 - a * l) * (m + q * l)) y k).1,
   8 * ((countLeW (fun l => (f - a * l) * (m + q * l)) y k).2
    + (countLeW (fun l => (f + 1 - a * l) * (m + q * l)) y k).2
    + (countLeW (fun l => (f + 2 - a * l) * (m + q * l)) y k).2) + 3)

theorem cnt3W_fst (y a q m f : ℤ) (k : ℕ) : (cnt3W y a q m f k).1 = cnt3 y a q m f k := by
  unfold cnt3W cnt3; simp only [countLeW_fst]

/-- `corr` with its cost. -/
def corrW (y n0 a q s : ℤ) (k ρ : ℕ) : ℤ × ℕ :=
  ((cnt3W y a q (n0 + ρ) ((s - a * ρ) / q) k).1 - k, (cnt3W y a q (n0 + ρ) ((s - a * ρ) / q) k).2 + 5)

theorem corrW_fst (y n0 a q s : ℤ) (k ρ : ℕ) : (corrW y n0 a q s k ρ).1 = corr y n0 a q s k ρ := by
  unfold corrW corr; rw [cnt3W_fst]

/-- `blockFast` with its cost. -/
def blockFastW (y n0 a q ainv : ℤ) (k : ℕ) : ℤ × ℕ :=
  ((2 * k * (q * y / n0) - k * (a + 1) * (q - 1) - a * q * k * (k - 1)) / 2
    + ∑ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ),
        (corrW y n0 a q (q * y / n0) k (clsRho ainv (q * y / n0) q j)).1,
   20 + ∑ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ),
        ((corrW y n0 a q (q * y / n0) k (clsRho ainv (q * y / n0) q j)).2 + 6))

theorem blockFastW_fst (y n0 a q ainv : ℤ) (k : ℕ) :
    (blockFastW y n0 a q ainv k).1 = blockFast y n0 a q ainv k := by
  unfold blockFastW blockFast; simp only [corrW_fst]

theorem blockFastW_cost (y n0 a q ainv : ℤ) (k : ℕ) :
    (blockFastW y n0 a q ainv k).2 ≤ 288 * Nat.log 2 (2 * k) + 134 := by
  unfold blockFastW
  dsimp only
  set m := Nat.log 2 (2 * k)
  have hc : ∀ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ),
      (corrW y n0 a q (q * y / n0) k (clsRho ainv (q * y / n0) q j)).2 + 6 ≤ 96 * m + 38 := by
    intro j _
    unfold corrW cnt3W
    dsimp only
    have e0 := countLeW_evals (fun l => (((q * y / n0 - a * (clsRho ainv (q * y / n0) q j : ℕ)) / q)
      - a * l) * ((n0 + (clsRho ainv (q * y / n0) q j : ℕ)) + q * l)) y k
    have e1 := countLeW_evals (fun l => (((q * y / n0 - a * (clsRho ainv (q * y / n0) q j : ℕ)) / q)
      + 1 - a * l) * ((n0 + (clsRho ainv (q * y / n0) q j : ℕ)) + q * l)) y k
    have e2 := countLeW_evals (fun l => (((q * y / n0 - a * (clsRho ainv (q * y / n0) q j : ℕ)) / q)
      + 2 - a * l) * ((n0 + (clsRho ainv (q * y / n0) q j : ℕ)) + q * l)) y k
    omega
  have hs := Finset.sum_le_card_nsmul _ _ _ hc
  have hcard : ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ).card ≤ 3 := Finset.card_le_three
  rw [smul_eq_mul] at hs
  have : ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ).card * (96 * m + 38) ≤ 3 * (96 * m + 38) :=
    Nat.mul_le_mul_right _ hcard
  omega

/-- `blockStep` with its cost. -/
def blockStepW (y r n0 : ℕ) : (ℕ × ℤ) × ℕ :=
  let R := r + 1 - n0
  let Q := (icbrtW (n0 ^ 3 / y)).1
  let a := (approxW y (n0 * n0) Q).1.1
  let q := (approxW y (n0 * n0) Q).1.2
  let c0 := 8 + (icbrtW (n0 ^ 3 / y)).2 + 6 * (approxW y (n0 * n0) Q).2
  if q = 0 ∨ Q < q ∨ R < q then ((R, direct y n0 R), c0 + R) else
  let k := min Q R / q
  let H := k * q
  let ainv : ℤ := (gcdAW a q).1
  let c1 := c0 + 6 * (gcdAW a q).2 + 20
  let D : ℤ := (q : ℤ) * y - (a : ℤ) * (n0 : ℤ) ^ 2
  if |D| * ((H : ℤ) - 1) < (n0 : ℤ) ^ 2 ∧ (q : ℤ) * y * ((H : ℤ) - 1) ^ 2 ≤ (n0 : ℤ) ^ 3 ∧
      ((a : ℤ) * ainv) % (q : ℤ) = 1 % (q : ℤ) then
    ((H, (blockFastW y n0 a q ainv k).1), c1 + (blockFastW y n0 a q ainv k).2)
  else ((H, direct y n0 H), c1 + H)

theorem blockStepW_fst (y r n0 : ℕ) : (blockStepW y r n0).1 = blockStep y r n0 := by
  unfold blockStepW blockStep
  simp only [icbrtW_fst, approxW_fst, gcdAW_fst, blockFastW_fst]
  split_ifs <;> rfl

/-- The per-block cost bound, `ℓ = Nat.log 2 y`. -/
def Bblk (y : ℕ) : ℕ := 320 * Nat.log 2 y + 500

lemma log_le_of_le {m y : ℕ} (h : m ≤ y) (k : ℕ) : Nat.log 2 (2 ^ k * m) ≤ Nat.log 2 y + k := by
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; have : m = 0 := by omega
    subst this; simp
  calc Nat.log 2 (2 ^ k * m) ≤ Nat.log 2 (y * 2 ^ k) := Nat.log_mono_right (by rw [mul_comm]; gcongr)
    _ = Nat.log 2 y + k := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by norm_num) (by positivity), ih]; ring

/-- **Cost of one block.** Under the routine's setup (`1 ≤ y`, `icbrt y < n0 ≤ isqrt y`) one block costs
at most `Bblk y + icbrt y`, and at most `Bblk y` unless it is the final direct tail. -/
theorem blockStepW_cost (y n0 : ℕ) (hy : 1 ≤ y) (hc : M2L3.icbrt y < n0) (hr : n0 ≤ Nat.sqrt y) :
    (blockStepW y (Nat.sqrt y) n0).2 ≤ Bblk y + M2L3.icbrt y ∧
    ((blockStepW y (Nat.sqrt y) n0).1.1 < Nat.sqrt y + 1 - n0 → (blockStepW y (Nat.sqrt y) n0).2 ≤ Bblk y) := by
  have hn : y < n0 ^ 3 := (lt_cube_iff y n0).1 hc
  obtain ⟨hQ1, hq1, hqQ, hchk⟩ := blockStep_checks y (Nat.sqrt y) n0 hy hn
  have hts := tail_short hy hr
  set ℓ := Nat.log 2 y
  have hn0 : 1 ≤ n0 := by omega
  have hnn : n0 * n0 ≤ y := Nat.le_sqrt.1 hr
  have hn0y : n0 ≤ y := by nlinarith
  have hdiv : n0 ^ 3 / y ≤ n0 := Nat.div_le_of_le_mul (by
    calc n0 ^ 3 = n0 * (n0 * n0) := by ring
      _ ≤ n0 * y := Nat.mul_le_mul_left _ hnn
      _ = y * n0 := by ring)
  set Q := icbrtF (n0 ^ 3 / y) with hQdef
  have hQy : Q ≤ y := by rw [hQdef, icbrtF_eq]; exact (M2L3.icbrt_le _).trans (hdiv.trans hn0y)
  have hQc : Q ≤ M2L3.icbrt y := M2L3.le_icbrt (le_trans (Nat.pow_le_pow_right (by omega) (by norm_num)) hts)
  -- the counters
  have ci : (icbrtW (n0 ^ 3 / y)).2 ≤ ℓ + 2 := by
    have := icbrtW_evals (n0 ^ 3 / y)
    have h2 := log_le_of_le (m := n0 ^ 3 / y + 1) (y := 2 * y) (by omega) 1
    have h3 : Nat.log 2 (2 * y) = ℓ + 1 := by rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    simp only [pow_one] at h2; omega
  have ca : (approxW y (n0 * n0) Q).2 ≤ 2 * ℓ + 3 := by
    have := approxW_steps y (n0 * n0) Q
    have : Nat.log 2 Q ≤ ℓ := Nat.log_mono_right hQy
    omega
  unfold blockStepW
  dsimp only
  simp only [icbrtW_fst, approxW_fst, gcdAW_fst]
  rw [← hQdef]
  set a := (approx y (n0 * n0) Q).1
  set q := (approx y (n0 * n0) Q).2
  unfold Bblk
  split_ifs with h1 h2
  · dsimp only
    refine ⟨by omega, fun h => by omega⟩
  · dsimp only
    push Not at h1
    have cg : (gcdAW a q).2 ≤ 2 * ℓ + 3 := by
      have := gcdAW_steps a q
      have := log_le_of_le (m := q) (y := y) (by omega) 1
      simp only [pow_one] at this; omega
    have cb := blockFastW_cost y n0 a q (Nat.gcdA a q) (min Q (Nat.sqrt y + 1 - n0) / q)
    have : Nat.log 2 (2 * (min Q (Nat.sqrt y + 1 - n0) / q)) ≤ ℓ + 1 := by
      have := log_le_of_le (m := min Q (Nat.sqrt y + 1 - n0) / q) (y := y)
        ((Nat.div_le_self _ _).trans ((min_le_left _ _).trans hQy)) 1
      simpa using this
    omega
  · exfalso
    push Not at h1
    exact h2 (hchk h1.2.2)

/-- `loop` with its cost (1 per call, plus the block costs). -/
def loopW (y r : ℕ) : ℕ → ℕ → ℤ × ℕ
  | 0, n0 => (direct y n0 (r + 1 - n0), r + 1 - n0)
  | fuel + 1, n0 =>
    if r < n0 then (0, 1) else
    ((blockStepW y r n0).1.2 + (loopW y r fuel (n0 + (blockStepW y r n0).1.1)).1,
     2 + (blockStepW y r n0).2 + (loopW y r fuel (n0 + (blockStepW y r n0).1.1)).2)

theorem loopW_fst (y r : ℕ) : ∀ fuel n0, (loopW y r fuel n0).1 = loop y r fuel n0 := by
  intro fuel
  induction fuel with
  | zero => intro n0; rfl
  | succ f ih =>
    intro n0
    rw [loopW, loop]
    split_ifs
    · rfl
    · dsimp only; rw [ih, blockStepW_fst]

theorem loopW_cost (y : ℕ) (hy : 1 ≤ y) : ∀ fuel n0, 1 ≤ n0 → n0 ≤ Nat.sqrt y + 1 →
    Nat.sqrt y + 1 ≤ n0 + fuel → (n0 ≤ Nat.sqrt y → M2L3.icbrt y < n0) →
    (loopW y (Nat.sqrt y) fuel n0).2
      ≤ nblocks y (Nat.sqrt y) fuel n0 * (Bblk y + 2) + M2L3.icbrt y + 1 := by
  intro fuel
  induction fuel with
  | zero => intro n0 _ _ h3 _; rw [loopW]; dsimp only; omega
  | succ f ih =>
    intro n0 h1 h2 h3 h4
    rw [loopW, nblocks]
    by_cases hr : Nat.sqrt y < n0
    · rw [ite_eq_left hr, ite_eq_left hr]; dsimp only; omega
    rw [ite_eq_right hr, ite_eq_right hr]
    dsimp only
    rw [← blockStepW_fst]
    have hc := h4 (by omega)
    obtain ⟨s1, s2, -⟩ := blockStep_spec y (Nat.sqrt y) n0 h1 (by omega)
    rw [← blockStepW_fst] at s1 s2
    obtain ⟨b1, b2⟩ := blockStepW_cost y n0 hy hc (by omega)
    set H := (blockStepW y (Nat.sqrt y) n0).1.1
    by_cases hfin : n0 + H = Nat.sqrt y + 1
    · -- the final block: the rest of the loop is a single check
      have hrest : (loopW y (Nat.sqrt y) f (n0 + H)).2 ≤ 1 := by
        rcases f with _ | g
        · rw [loopW]; dsimp only; omega
        · rw [loopW, ite_eq_left (by omega)]
      have : (nblocks y (Nat.sqrt y) f (n0 + H) + 1) * (Bblk y + 2)
          = nblocks y (Nat.sqrt y) f (n0 + H) * (Bblk y + 2) + (Bblk y + 2) := by ring
      rw [add_comm 1, this]
      omega
    · have hb := b2 (by omega)
      have := ih (n0 + H) (by omega) (by omega) (by omega) (fun _ => by omega)
      have e : (nblocks y (Nat.sqrt y) f (n0 + H) + 1) * (Bblk y + 2)
          = nblocks y (Nat.sqrt y) f (n0 + H) * (Bblk y + 2) + (Bblk y + 2) := by ring
      rw [add_comm 1, e]
      omega

/-- `blockSZ` with its cost: `Nat.sqrt y` charged `2 log2 y + 2`, `icbrtF y` measured, the direct
columns 1 each, then the loop. -/
def blockSZW (y L : ℕ) : ℤ × ℕ :=
  (direct y (L + 1) (max (L + 1) (min ((icbrtW y).1 + 1) (Nat.sqrt y + 1)) - (L + 1))
      + (loopW y (Nat.sqrt y) (Nat.sqrt y + 1) (max (L + 1) (min ((icbrtW y).1 + 1) (Nat.sqrt y + 1)))).1,
   (2 * Nat.log 2 y + 2) + (icbrtW y).2 + 6
      + (max (L + 1) (min ((icbrtW y).1 + 1) (Nat.sqrt y + 1)) - (L + 1))
      + (loopW y (Nat.sqrt y) (Nat.sqrt y + 1) (max (L + 1) (min ((icbrtW y).1 + 1) (Nat.sqrt y + 1)))).2)

/-- **The instrumented copy agrees with `blockSZ`.** -/
theorem blockSZW_fst (y L : ℕ) : (blockSZW y L).1 = blockSZ y L := by
  unfold blockSZW blockSZ
  simp only [icbrtW_fst, loopW_fst]

/-- **Target 4: total work of `blockSZ`.** For every `y ≥ 1` and every `L`, the instrumented run of
`blockSZ y L` costs at most `2000 (icbrt y + 1) (Nat.log 2 y + 2) ^ 2`, that is
`O(y^(1/3) log^2 y)`, uniformly in `L`. -/
theorem blockSZW_cost (y L : ℕ) (hy : 1 ≤ y) :
    (blockSZW y L).2 ≤ 2000 * (M2L3.icbrt y + 1) * (Nat.log 2 y + 2) ^ 2 := by
  unfold blockSZW
  dsimp only
  rw [icbrtW_fst]
  set ℓ := Nat.log 2 y
  set c0 := M2L3.icbrt y
  set n1 := max (L + 1) (min (icbrtF y + 1) (Nat.sqrt y + 1)) with hn1
  have hic : icbrtF y = c0 := icbrtF_eq y
  have ci : (icbrtW y).2 ≤ ℓ + 2 := by
    have := icbrtW_evals y
    have h2 := log_le_of_le (m := y + 1) (y := 2 * y) (by omega) 1
    have h3 : Nat.log 2 (2 * y) = ℓ + 1 := by rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    simp only [pow_one] at h2; omega
  have hdirect : n1 - (L + 1) ≤ c0 := by rw [hn1, hic]; omega
  have hloop : (loopW y (Nat.sqrt y) (Nat.sqrt y + 1) n1).2
      ≤ nblocks y (Nat.sqrt y) (Nat.sqrt y + 1) n1 * (Bblk y + 2) + c0 + 1 := by
    by_cases h : n1 ≤ Nat.sqrt y + 1
    · exact loopW_cost y hy (Nat.sqrt y + 1) n1 (by omega) h (by omega)
        (by intro h; rw [hn1, hic] at h ⊢; omega)
    · rw [loopW, ite_eq_left (by omega)]; omega
  have hnb : nblocks y (Nat.sqrt y) (Nat.sqrt y + 1) n1 ≤ 4 * (c0 + 1) * (ℓ + 2) + 1 := by
    have := blockSZ_nblocks y L hy; rw [← hn1] at this; exact this
  have hB : Bblk y + 2 ≤ 330 * (ℓ + 2) := by unfold Bblk; omega
  have hprod : nblocks y (Nat.sqrt y) (Nat.sqrt y + 1) n1 * (Bblk y + 2) ≤ (4 * (c0 + 1) * (ℓ + 2) + 1) * (330 * (ℓ + 2)) :=
    Nat.mul_le_mul hnb hB
  set X := (c0 + 1) * (ℓ + 2) ^ 2 with hX
  have e1 : (4 * (c0 + 1) * (ℓ + 2) + 1) * (330 * (ℓ + 2)) = 1320 * X + 330 * (ℓ + 2) := by
    rw [hX]; ring
  have e2 : 2000 * (c0 + 1) * (ℓ + 2) ^ 2 = 2000 * X := by rw [hX]; ring
  have x1 : ℓ + 2 ≤ X := by
    rw [hX]
    calc ℓ + 2 ≤ (ℓ + 2) * (ℓ + 2) := Nat.le_mul_of_pos_right _ (by omega)
      _ = 1 * (ℓ + 2) ^ 2 := by ring
      _ ≤ (c0 + 1) * (ℓ + 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have x2 : c0 + 1 ≤ X := by
    rw [hX]
    calc c0 + 1 = (c0 + 1) * 1 := by ring
      _ ≤ (c0 + 1) * (ℓ + 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
  rw [e2]
  omega

end M2L6c

#print axioms M2L6c.approx_good
#print axioms M2L6c.approx_inv
#print axioms M2L6c.blockStep_checks
#print axioms M2L6c.blockStep_fast
#print axioms M2L6c.blockStep_tail
#print axioms M2L6c.tail_short
#print axioms M2L6c.blockStep_progress
#print axioms M2L6c.nblocks_le_pot
#print axioms M2L6c.nblocks_le
#print axioms M2L6c.blockSZ_nblocks
#print axioms M2L6c.bfirstW_fst
#print axioms M2L6c.bfirstW_evals
#print axioms M2L6c.icbrtW_fst
#print axioms M2L6c.icbrtW_evals
#print axioms M2L6c.approxW_fst
#print axioms M2L6c.approxW_steps
#print axioms M2L6c.gcdAW_fst
#print axioms M2L6c.gcdAW_steps
#print axioms M2L6c.countLeW_fst
#print axioms M2L6c.countLeW_evals
#print axioms M2L6c.cnt3W_fst
#print axioms M2L6c.blockFastW_fst
#print axioms M2L6c.blockFastW_cost
#print axioms M2L6c.blockStepW_fst
#print axioms M2L6c.blockStepW_cost
#print axioms M2L6c.loopW_fst
#print axioms M2L6c.loopW_cost
#print axioms M2L6c.blockSZW_fst
#print axioms M2L6c.blockSZW_cost
