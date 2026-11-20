/-
  Seat M2L5, item 1: the certified D_3 algorithm (m2/e/PROOF_D3_5_9.md).
  A computable block routine `blockS y L` for S(y, L) = sum_{L < b <= isqrt y} floor(y / b),
  proved equal to that sum for every y and L, and `D3fast`, proved equal to D_3 for every x,
  via (F1) of round 3 (M2L3.ternary_F1). Then `piMod3`, proved equal to pi(x) mod 3 via round 4.
-/
import Mathlib
import M2ResultM

open Finset

namespace M2L5

/-! ## A verified binary search -/

/-- `bfirst p lo hi`: binary search on `[lo, hi]`; for `p` monotone on `[lo, hi]` it returns the least
`i` in `[lo, hi]` with `p i`, or `hi` if there is none. -/
def bfirst (p : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if h : lo < hi then
    if p ((lo + hi) / 2) then bfirst p lo ((lo + hi) / 2) else bfirst p ((lo + hi) / 2 + 1) hi
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem bfirst_spec (p : ℕ → Bool) : ∀ (n lo hi : ℕ), hi - lo = n → lo ≤ hi →
    (∀ i j, lo ≤ i → i ≤ j → j ≤ hi → p i = true → p j = true) →
    lo ≤ bfirst p lo hi ∧ bfirst p lo hi ≤ hi ∧
    (∀ i, lo ≤ i → i < bfirst p lo hi → p i = false) ∧
    (p (bfirst p lo hi) = true ∨ bfirst p lo hi = hi) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lo hi hn hle hmono
  rw [bfirst]
  by_cases h1 : lo < hi
  · rw [dif_pos h1]
    by_cases h2 : p ((lo + hi) / 2) = true
    · rw [if_pos h2]
      obtain ⟨a1, a2, a3, a4⟩ := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
        (by omega) (fun i j hi1 hij hj => hmono i j hi1 hij (by omega))
      refine ⟨a1, by omega, a3, ?_⟩
      rcases a4 with h | h
      · exact Or.inl h
      · left; rw [h]; exact h2
    · rw [if_neg h2]
      obtain ⟨a1, a2, a3, a4⟩ := ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl
        (by omega) (fun i j hi1 hij hj => hmono i j (by omega) hij hj)
      refine ⟨by omega, a2, ?_, a4⟩
      intro i hi1 hi2
      by_cases hc : i ≤ (lo + hi) / 2
      · cases hpi : p i
        · rfl
        · exact absurd (hmono i _ hi1 hc (by omega) hpi) h2
      · exact a3 i (by omega) hi2
  · rw [dif_neg h1]
    exact ⟨le_rfl, hle, fun i h1 h2 => absurd h2 (by omega), Or.inr (by omega)⟩

/-! ## Fast integer cube root -/

/-- Integer cube root by bisection. -/
def icbrtF (n : ℕ) : ℕ := bfirst (fun m => decide (n < m ^ 3)) 0 (n + 1) - 1

theorem icbrtF_eq (n : ℕ) : icbrtF n = M2L3.icbrt n := by
  obtain ⟨a1, a2, a3, a4⟩ := bfirst_spec (fun m => decide (n < m ^ 3)) (n + 1) 0 (n + 1) rfl
    (by omega) (fun i j _ hij _ hi => by
      simp only [decide_eq_true_eq] at hi ⊢
      exact lt_of_lt_of_le hi (Nat.pow_le_pow_left hij 3))
  set r := bfirst (fun m => decide (n < m ^ 3)) 0 (n + 1)
  have hr : n < r ^ 3 := by
    rcases a4 with h | h
    · simpa using h
    · rw [h]
      calc n < n + 1 := by omega
        _ = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hr0 : r ≠ 0 := by rintro h; rw [h] at hr; simp at hr
  have hlow : (r - 1) ^ 3 ≤ n := by
    have := a3 (r - 1) (by omega) (by omega)
    simpa using this
  unfold icbrtF
  apply le_antisymm
  · exact M2L3.le_icbrt hlow
  · by_contra hc
    have : r ≤ M2L3.icbrt n := by omega
    have := (Nat.pow_le_pow_left this 3).trans (M2L3.icbrt_pow_le n)
    omega

/-! ## Concave counting -/

/-- `#{l < k : P l ≤ y}` for `P` with nonincreasing differences: the argmax `ls` by bisection on the
difference, then the two ends of the superlevel set `{P > y}` by bisection (PROOF Lemma 6). -/
def countLe (P : ℕ → ℤ) (y : ℤ) (k : ℕ) : ℕ :=
  if k = 0 then 0 else
  let ls := bfirst (fun l => decide (P (l + 1) - P l ≤ 0)) 0 (k - 1)
  if P ls ≤ y then k else
  let left := bfirst (fun l => decide (y < P l)) 0 ls
  let right := bfirst (fun l => decide (l = k ∨ P l ≤ y)) ls k
  k - (right - left)

section Concave
variable (P : ℕ → ℤ) (hc : ∀ l, P (l + 2) - P (l + 1) ≤ P (l + 1) - P l)
include hc

lemma diff_anti : ∀ i j, i ≤ j → P (j + 1) - P j ≤ P (i + 1) - P i := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (hc j).trans ih

theorem countLe_spec (y : ℤ) (k : ℕ) :
    (countLe P y k : ℤ) = ∑ l ∈ range k, (if P l ≤ y then (1 : ℤ) else 0) := by
  rw [sum_boole]
  unfold countLe
  by_cases hk : k = 0
  · subst hk; simp
  rw [if_neg hk]
  dsimp only
  obtain ⟨b1, b2, b3, b4⟩ := bfirst_spec (fun l => decide (P (l + 1) - P l ≤ 0)) (k - 1) 0 (k - 1)
    (by omega) (by omega) (fun i j _ hij _ hi => by
      simp only [decide_eq_true_eq] at hi ⊢
      exact (diff_anti P hc i j hij).trans hi)
  set ls := bfirst (fun l => decide (P (l + 1) - P l ≤ 0)) 0 (k - 1)
  -- P nondecreasing on [0, ls]
  have hup : ∀ i j, i ≤ j → j ≤ ls → P i ≤ P j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj' ih =>
      have := b3 j (by omega) (by omega)
      simp only [decide_eq_false_iff_not, not_le] at this
      linarith [ih (by omega)]
  -- P nonincreasing on [ls, k-1]
  have hdown : ∀ i j, ls ≤ i → i ≤ j → j ≤ k - 1 → P j ≤ P i := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj' ih =>
      have hd : P (ls + 1) - P ls ≤ 0 := by
        rcases b4 with h | h
        · simpa using h
        · omega
      have := (diff_anti P hc ls j (by omega)).trans hd
      linarith [ih (by omega)]
  by_cases hmax : P ls ≤ y
  · rw [if_pos hmax]
    congr 1
    rw [filter_true_of_mem, card_range]
    intro l hl
    rw [mem_range] at hl
    rcases le_total l ls with h | h
    · exact (hup l ls h le_rfl).trans hmax
    · exact (hdown ls l le_rfl h (by omega)).trans hmax
  rw [if_neg hmax]
  push Not at hmax
  obtain ⟨c1, c2, c3, c4⟩ := bfirst_spec (fun l => decide (y < P l)) ls 0 ls (by omega) (by omega)
    (fun i j _ hij hj hi => by
      simp only [decide_eq_true_eq] at hi ⊢
      exact lt_of_lt_of_le hi (hup i j hij hj))
  set left := bfirst (fun l => decide (y < P l)) 0 ls
  obtain ⟨d1, d2, d3, d4⟩ := bfirst_spec (fun l => decide (l = k ∨ P l ≤ y)) (k - ls) ls k rfl
    (by omega) (fun i j hi hij hj hpi => by
      simp only [decide_eq_true_eq] at hpi ⊢
      rcases hpi with h | h
      · left; omega
      · by_cases hjk : j = k
        · exact Or.inl hjk
        · exact Or.inr ((hdown i j hi hij (by omega)).trans h))
  set right := bfirst (fun l => decide (l = k ∨ P l ≤ y)) ls k
  have hPleft : y < P left := by
    rcases c4 with h | h
    · simpa using h
    · rw [h]; exact hmax
  have hright_gt : ls < right := by
    by_contra hc'
    have : right = ls := by omega
    rcases d4 with h | h
    · rw [this] at h; simp at h; omega
    · omega
  have hset : (range k).filter (fun l => ¬ P l ≤ y) = Ico left right := by
    ext l
    simp only [mem_filter, mem_range, mem_Ico, not_le]
    constructor
    · rintro ⟨hl, hpl⟩
      constructor
      · by_contra h
        push Not at h
        have := c3 l (by omega) h
        simp only [decide_eq_false_iff_not, not_lt] at this
        linarith
      · by_contra h
        push Not at h
        -- right ≤ l < k: right ≠ k, so P right ≤ y
        have hrk : right ≠ k := by omega
        have hPr : P right ≤ y := by
          rcases d4 with h' | h'
          · simp only [decide_eq_true_eq] at h'
            rcases h' with h'' | h''
            · exact absurd h'' hrk
            · exact h''
          · exact absurd h' hrk
        have := hdown right l (by omega) h (by omega)
        linarith
    · rintro ⟨hl1, hl2⟩
      refine ⟨by omega, ?_⟩
      rcases le_total l ls with h | h
      · exact lt_of_lt_of_le hPleft (hup left l hl1 h)
      · have := d3 l h hl2
        simp only [decide_eq_false_iff_not, not_or, not_le] at this
        exact this.2
  have hcard := card_filter_add_card_filter_not (s := range k) (fun l => P l ≤ y)
  rw [hset, Nat.card_Ico, card_range] at hcard
  have : left ≤ right := by omega
  omega

end Concave

/-! ## The error window (PROOF Lemmas 1 and 3, as integer inequalities) -/

theorem window {y n0 q a s t r0 D : ℤ} (hn0 : 0 < n0) (ht : 0 ≤ t) (hy : 0 ≤ y) (hq : 0 < q)
    (hs : q * y = s * n0 + r0) (hr0 : 0 ≤ r0) (hr1 : r0 < n0) (hD : D = q * y - a * n0 ^ 2)
    (h1 : |D| * t < n0 ^ 2) (h2 : q * y * t ^ 2 ≤ n0 ^ 3) :
    (s - a * t - 1) * (n0 + t) < q * y ∧ q * y < (s - a * t + 3) * (n0 + t) := by
  have key : n0 ^ 2 * (q * y - (s - a * t) * (n0 + t))
      = q * y * t ^ 2 + r0 * (n0 + t) * n0 - D * t * (n0 + t) := by
    rw [hD]; linear_combination (n0 * (n0 + t)) * hs
  have hn : 0 < n0 + t := by linarith
  have hDt : D * t < n0 ^ 2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_abs_self D) ht) h1
  have hDt' : -(D * t) < n0 ^ 2 := by
    have : -(D * t) = (-D) * t := by ring
    rw [this]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (neg_le_abs D) ht) h1
  have hqy : 0 ≤ q * y * t ^ 2 := by positivity
  have hr0n : 0 ≤ r0 * (n0 + t) * n0 := by positivity
  have hn02 : 0 < n0 ^ 2 := by positivity
  constructor
  · have e1 : D * t * (n0 + t) < n0 ^ 2 * (n0 + t) := mul_lt_mul_of_pos_right hDt hn
    have : 0 < n0 ^ 2 * (q * y - (s - a * t - 1) * (n0 + t)) := by nlinarith
    have := pos_of_mul_pos_right this hn02.le
    linarith
  · have e1 : -(D * t) * (n0 + t) < n0 ^ 2 * (n0 + t) := mul_lt_mul_of_pos_right hDt' hn
    have e2 : r0 * (n0 + t) * n0 < n0 * (n0 + t) * n0 := by
      have := mul_lt_mul_of_pos_right hr1 (mul_pos hn hn0)
      nlinarith
    have e3 : n0 ^ 3 ≤ n0 ^ 2 * (n0 + t) := by nlinarith
    have : 0 < n0 ^ 2 * ((s - a * t + 3) * (n0 + t) - q * y) := by nlinarith
    have := pos_of_mul_pos_right this hn02.le
    linarith

/-- From the window: `q floor(y/n) ≤ N + 2` and `N ≤ q floor(y/n) + q`. -/
theorem floor_window {y n q N : ℤ} (hn : 0 < n) (hq : 0 < q)
    (hlo : (N - 1) * n < q * y) (hhi : q * y < (N + 3) * n) :
    q * (y / n) ≤ N + 2 ∧ N ≤ q * (y / n) + q := by
  have g1 : y / n * n ≤ y := Int.ediv_mul_le y hn.ne'
  have g2 : y < (y / n + 1) * n := Int.lt_ediv_add_one_mul_self y hn
  constructor
  · have : q * (y / n) * n < (N + 3) * n := by nlinarith
    have := lt_of_mul_lt_mul_right this hn.le
    omega
  · have : (N - 1) * n < (q * (y / n) + q) * n := by nlinarith
    have := lt_of_mul_lt_mul_right this hn.le
    omega

/-- Non-exceptional classes (PROOF Lemma 3'): if `1 ≤ N mod q ≤ q - 3` then `floor(y/n) = floor(N/q)`. -/
theorem floor_eq_of_class {G q N : ℤ} (hq : 0 < q) (hA : q * G ≤ N + 2) (hB : N ≤ q * G + q)
    (hj1 : 1 ≤ N % q) (hj2 : N % q ≤ q - 3) : G = N / q := by
  have hN := Int.mul_ediv_add_emod N q
  have hlt : q * G < q * (N / q + 1) := by nlinarith
  have hgt : q * (N / q) < q * (G + 1) := by nlinarith
  have := lt_of_mul_lt_mul_left hlt hq.le
  have := lt_of_mul_lt_mul_left hgt hq.le
  omega

/-- Exceptional classes (PROOF Lemma 5): `floor(N/q) - 1 ≤ floor(y/n) ≤ floor(N/q) + 2`. -/
theorem floor_range {G q N : ℤ} (hq : 0 < q) (hA : q * G ≤ N + 2) (hB : N ≤ q * G + q) :
    N / q - 1 ≤ G ∧ G ≤ N / q + 2 := by
  have hN := Int.mul_ediv_add_emod N q
  have hj0 : 0 ≤ N % q := Int.emod_nonneg N hq.ne'
  have hj1 : N % q < q := Int.emod_lt_of_pos N hq
  have hlt : q * G < q * (N / q + 3) := by nlinarith
  have hgt : q * (N / q) < q * (G + 2) := by nlinarith
  have := lt_of_mul_lt_mul_left hlt hq.le
  have := lt_of_mul_lt_mul_left hgt hq.le
  omega

/-- The level decomposition: `G = (c - 1) + [c ≤ G] + [c + 1 ≤ G] + [c + 2 ≤ G]` for `c - 1 ≤ G ≤ c + 2`. -/
theorem level_decomp {G c : ℤ} (h1 : c - 1 ≤ G) (h2 : G ≤ c + 2) :
    G = (c - 1) + ((if c ≤ G then 1 else 0) + (if c + 1 ≤ G then 1 else 0)
      + (if c + 2 ≤ G then 1 else 0)) := by
  have : G = c - 1 ∨ G = c ∨ G = c + 1 ∨ G = c + 2 := by omega
  rcases this with h | h | h | h <;> subst h <;> simp <;> omega

/-! ## The block routine -/

/-- Last continued-fraction convergent `p/q` of `u/v` with `q ≤ Q` (Euclid, with fuel). -/
def approxAux (Q : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, _, _, _, _, _, _, best => best
  | fuel + 1, u, v, p0, q0, p1, q1, best =>
    if v = 0 then best else
    if Q < u / v * q1 + q0 then best
    else approxAux Q fuel v (u % v) p1 q1 (u / v * p1 + p0) (u / v * q1 + q0)
      (u / v * p1 + p0, u / v * q1 + q0)

/-- `(a, q)`: the last convergent of `u / v` with denominator at most `Q` (PROOF Lemma 2). -/
def approx (u v Q : ℕ) : ℕ × ℕ := approxAux Q (2 * Nat.log2 v + 8) u v 0 1 1 0 (0, 0)

/-- Direct columns: `∑_{n0 ≤ b < n0 + len} floor(y / b)`. -/
def direct (y n0 len : ℕ) : ℤ := ∑ b ∈ Ico n0 (n0 + len), ((y / b : ℕ) : ℤ)

/-- The three level counts of one residue class (PROOF Lemma 5): `∑_{T = f}^{f+2} #{l < k : (T - a l)(m + q l) ≤ y}`. -/
def cnt3 (y a q m f : ℤ) (k : ℕ) : ℤ :=
  (countLe (fun l => (f - a * l) * (m + q * l)) y k : ℤ)
    + (countLe (fun l => (f + 1 - a * l) * (m + q * l)) y k : ℤ)
    + (countLe (fun l => (f + 2 - a * l) * (m + q * l)) y k : ℤ)

/-- The class `ρ = a⁻¹ (s - j) mod q` of the offsets `t` with `(s - a t) mod q = j`. -/
def clsRho (ainv s q j : ℤ) : ℕ := ((ainv * (s - j)) % q).toNat

/-- The correction of class `ρ`: counts minus `k`. -/
def corr (y n0 a q s : ℤ) (k ρ : ℕ) : ℤ := cnt3 y a q (n0 + ρ) ((s - a * ρ) / q) k - k

/-- The fast block sum over `n0 ≤ n < n0 + k q`: linear part (PROOF Lemma 4) plus the corrections of the
classes `j ∈ J = {0, q - 2, q - 1} (mod q)` (PROOF Lemmas 3', 5, 6). -/
def blockFast (y n0 a q ainv : ℤ) (k : ℕ) : ℤ :=
  (2 * k * (q * y / n0) - k * (a + 1) * (q - 1) - a * q * k * (k - 1)) / 2
    + ∑ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ),
        corr y n0 a q (q * y / n0) k (clsRho ainv (q * y / n0) q j)

/-- One block starting at `n0 ≤ r`: returns its length `H ≥ 1` and its sum. The hypotheses of the
window lemma are checked at run time (they hold by PROOF Lemmas 2 and 3); if a check fails the block
is summed directly, so correctness never depends on the checks. -/
def blockStep (y r n0 : ℕ) : ℕ × ℤ :=
  let R := r + 1 - n0
  let Q := icbrtF (n0 ^ 3 / y)
  let aq := approx y (n0 * n0) Q
  let a := aq.1
  let q := aq.2
  if q = 0 ∨ Q < q ∨ R < q then (R, direct y n0 R) else
  let k := min Q R / q
  let H := k * q
  let ainv : ℤ := Nat.gcdA a q
  let D : ℤ := (q : ℤ) * y - (a : ℤ) * (n0 : ℤ) ^ 2
  if |D| * ((H : ℤ) - 1) < (n0 : ℤ) ^ 2 ∧ (q : ℤ) * y * ((H : ℤ) - 1) ^ 2 ≤ (n0 : ℤ) ^ 3 ∧
      ((a : ℤ) * ainv) % (q : ℤ) = 1 % (q : ℤ) then
    (H, blockFast y n0 a q ainv k)
  else (H, direct y n0 H)

/-- The block loop from `n0` to `r` (fuel `r + 1` suffices since every block has length at least 1;
on exhausted fuel the rest is summed directly, so the result is exact for any fuel). -/
def loop (y r : ℕ) : ℕ → ℕ → ℤ
  | 0, n0 => direct y n0 (r + 1 - n0)
  | fuel + 1, n0 =>
    if r < n0 then 0 else
    let p := blockStep y r n0
    p.2 + loop y r fuel (n0 + p.1)

/-- The routine `S(y, L)` as an integer: direct columns for `b ≤ min(icbrt y, isqrt y)`, then blocks. -/
def blockSZ (y L : ℕ) : ℤ :=
  let r := Nat.sqrt y
  let n1 := max (L + 1) (min (icbrtF y + 1) (r + 1))
  direct y (L + 1) (n1 - (L + 1)) + loop y r (r + 1) n1

/-- **The block routine** `blockS y L`, a computable function of naturals. -/
def blockS (y L : ℕ) : ℕ := (blockSZ y L).toNat

/-! ## Correctness of one block -/

lemma sum_split (g : ℕ → ℤ) (q : ℕ) : ∀ k : ℕ,
    ∑ t ∈ range (k * q), g t = ∑ ρ ∈ range q, ∑ l ∈ range k, g (ρ + q * l)
  | 0 => by simp
  | k + 1 => by
    rw [show (k + 1) * q = k * q + q by ring, sum_range_add, sum_split g q k]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    congr 1; ring

lemma two_sum_range (n : ℕ) : 2 * ∑ i ∈ range n, (i : ℤ) = n * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

section Classes
variable {a q ainv s : ℤ} (hq : 0 < q) (hinv : (a * ainv) % q = 1 % q)
include hq hinv

lemma j_of_cls {j : ℤ} (hj0 : 0 ≤ j) (hj1 : j < q) :
    (s - a * (clsRho ainv s q j : ℤ)) % q = j := by
  unfold clsRho
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')]
  have h1 : (ainv * (s - j)) % q ≡ ainv * (s - j) [ZMOD q] := Int.mod_modEq _ _
  have h2 : a * ainv ≡ 1 [ZMOD q] := hinv
  have h3 : s - a * ((ainv * (s - j)) % q) ≡ s - 1 * (s - j) [ZMOD q] := by
    refine Int.ModEq.sub_left s ?_
    refine (h1.mul_left a).trans ?_
    rw [← mul_assoc]; exact h2.mul_right _
  have h4 : s - 1 * (s - j) = j := by ring
  rw [h4] at h3
  rw [h3, Int.emod_eq_of_lt hj0 hj1]

lemma cls_of_j {ρ : ℕ} (hρ : (ρ : ℤ) < q) : clsRho ainv s q ((s - a * ρ) % q) = ρ := by
  unfold clsRho
  have h1 : (s - a * ρ) % q ≡ s - a * ρ [ZMOD q] := Int.mod_modEq _ _
  have h2 : a * ainv ≡ 1 [ZMOD q] := hinv
  have h3 : ainv * (s - (s - a * ρ) % q) ≡ ainv * (s - (s - a * ρ)) [ZMOD q] :=
    (Int.ModEq.sub_left s h1).mul_left _
  have h4 : ainv * (s - (s - a * ρ)) = (a * ainv) * ρ := by ring
  rw [h4] at h3
  have h5 := h3.trans (h2.mul_right (ρ : ℤ))
  rw [one_mul] at h5
  rw [h5, Int.emod_eq_of_lt (by positivity) hρ]
  simp

lemma sum_residues : ∑ ρ ∈ range q.toNat, (s - a * ρ) % q = ∑ v ∈ range q.toNat, (v : ℤ) := by
  have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  refine sum_nbij' (fun ρ => ((s - a * ρ) % q).toNat) (fun v => clsRho ainv s q v) ?_ ?_ ?_ ?_ ?_
  · intro ρ _
    simp only [mem_range]
    have := Int.emod_lt_of_pos (s - a * ρ) hq
    have := Int.emod_nonneg (s - a * ρ) hq.ne'
    omega
  · intro v hv
    simp only [mem_range] at hv ⊢
    unfold clsRho
    have := Int.emod_lt_of_pos (ainv * (s - v)) hq
    have := Int.emod_nonneg (ainv * (s - v)) hq.ne'
    omega
  · intro ρ hρ
    simp only [mem_range] at hρ
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')]
    exact cls_of_j hq hinv (by omega)
  · intro v hv
    simp only [mem_range] at hv
    rw [j_of_cls hq hinv (by positivity) (by omega)]
    simp
  · intro ρ _
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')]

/-- PROOF Lemma 4, summed over the classes: `2 ∑_{ρ < q} floor((s - a ρ)/q) = 2 s - (a + 1)(q - 1)`. -/
lemma two_sum_floor : 2 * ∑ ρ ∈ range q.toNat, (s - a * ρ) / q = 2 * s - (a + 1) * (q - 1) := by
  have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  have e1 : ∀ ρ : ℕ, q * ((s - a * ρ) / q) = (s - a * ρ) - (s - a * ρ) % q := by
    intro ρ; have := Int.mul_ediv_add_emod (s - a * ρ) q; linarith
  have e2 : q * ∑ ρ ∈ range q.toNat, (s - a * ρ) / q
      = q.toNat * s - a * ∑ ρ ∈ range q.toNat, (ρ : ℤ) - ∑ v ∈ range q.toNat, (v : ℤ) := by
    rw [mul_sum, sum_congr rfl fun ρ _ => e1 ρ, sum_sub_distrib, sum_residues hq hinv,
      sum_sub_distrib, sum_const, card_range, mul_sum]
    simp
  have e3 := two_sum_range q.toNat
  rw [hqn] at e2 e3
  have : q * (2 * ∑ ρ ∈ range q.toNat, (s - a * ρ) / q) = q * (2 * s - (a + 1) * (q - 1)) := by
    linear_combination 2 * e2 - (a + 1) * e3
  exact mul_left_cancel₀ hq.ne' this

lemma notJ {j : ℤ} (hj0 : 0 ≤ j) (hj1 : j < q)
    (hJ : j ∉ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ)) : 1 ≤ j ∧ j ≤ q - 3 := by
  simp only [mem_insert, mem_singleton, not_or] at hJ
  obtain ⟨h0, h1, h2⟩ := hJ
  rcases (show q = 1 ∨ q = 2 ∨ 3 ≤ q by omega) with h | h | h
  · subst h; omega
  · subst h; norm_num at h1 h2; omega
  · rw [Int.emod_eq_of_lt (by omega) (by omega)] at h1
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h2
    omega

end Classes

lemma concaveP {a q : ℤ} (ha : 0 ≤ a) (hq : 0 ≤ q) (T m : ℤ) : ∀ l : ℕ,
    (T - a * ((l + 2 : ℕ) : ℤ)) * (m + q * ((l + 2 : ℕ) : ℤ)) - (T - a * ((l + 1 : ℕ) : ℤ)) * (m + q * ((l + 1 : ℕ) : ℤ))
      ≤ (T - a * ((l + 1 : ℕ) : ℤ)) * (m + q * ((l + 1 : ℕ) : ℤ)) - (T - a * (l : ℤ)) * (m + q * (l : ℤ)) := by
  intro l
  have key : ((T - a * ((l + 2 : ℕ) : ℤ)) * (m + q * ((l + 2 : ℕ) : ℤ)) - (T - a * ((l + 1 : ℕ) : ℤ)) * (m + q * ((l + 1 : ℕ) : ℤ)))
      - ((T - a * ((l + 1 : ℕ) : ℤ)) * (m + q * ((l + 1 : ℕ) : ℤ)) - (T - a * (l : ℤ)) * (m + q * (l : ℤ)))
      = -2 * (a * q) := by push_cast; ring
  linarith [mul_nonneg ha hq]

/-- **Block correctness.** Under the window hypotheses (checked in `blockStep`), the fast block sum equals
`∑_{0 ≤ t < k q} floor(y / (n0 + t))`. -/
theorem blockFast_spec {y n0 a q ainv : ℤ} {k : ℕ} (hy : 0 ≤ y) (hn0 : 0 < n0) (ha : 0 ≤ a)
    (hq : 0 < q) (hinv : (a * ainv) % q = 1 % q)
    (h1 : |q * y - a * n0 ^ 2| * ((k * q.toNat : ℕ) - 1 : ℤ) < n0 ^ 2)
    (h2 : q * y * ((k * q.toNat : ℕ) - 1 : ℤ) ^ 2 ≤ n0 ^ 3) :
    blockFast y n0 a q ainv k = ∑ t ∈ range (k * q.toNat), y / (n0 + t) := by
  have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  set s := q * y / n0 with hs_def
  set r0 := q * y % n0
  have hs : q * y = s * n0 + r0 := by have := Int.mul_ediv_add_emod (q * y) n0; linarith
  have hr0 : 0 ≤ r0 := Int.emod_nonneg _ hn0.ne'
  have hr1 : r0 < n0 := Int.emod_lt_of_pos _ hn0
  -- the window for every offset t < k q
  have hwin : ∀ t : ℕ, t < k * q.toNat →
      q * (y / (n0 + t)) ≤ (s - a * t) + 2 ∧ (s - a * t) ≤ q * (y / (n0 + t)) + q := by
    intro t ht
    have htH : (t : ℤ) ≤ ((k * q.toNat : ℕ) : ℤ) - 1 := by
      have : (t : ℤ) < ((k * q.toNat : ℕ) : ℤ) := by exact_mod_cast ht
      linarith
    have ht0 : (0 : ℤ) ≤ t := by positivity
    have hw := window (a := a) (t := t) hn0 ht0 hy hq hs hr0 hr1 rfl
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left htH (abs_nonneg _)) h1)
      (le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 htH 2) (by positivity)) h2)
    exact floor_window (by linarith) hq (by linarith [hw.1]) hw.2
  rw [sum_split]
  -- per class
  have hrow : ∀ ρ ∈ range q.toNat, ∑ l ∈ range k, y / (n0 + ((ρ + q.toNat * l : ℕ) : ℤ))
      = ∑ l ∈ range k, ((s - a * ρ) / q - a * l) + corr y n0 a q s k ρ := by
    intro ρ hρ
    rw [mem_range] at hρ
    unfold corr cnt3
    rw [countLe_spec _ (concaveP ha hq.le _ _), countLe_spec _ (concaveP ha hq.le _ _),
      countLe_spec _ (concaveP ha hq.le _ _)]
    rw [← sum_add_distrib, ← sum_add_distrib]
    have : (k : ℤ) = ∑ l ∈ range k, (1 : ℤ) := by simp
    rw [this, add_sub_assoc', ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun l hl => ?_
    rw [mem_range] at hl
    have htk : ρ + q.toNat * l < k * q.toNat := by nlinarith
    obtain ⟨hA, hB⟩ := hwin _ htk
    set G := y / (n0 + ((ρ + q.toNat * l : ℕ) : ℤ))
    have hN : s - a * ((ρ + q.toNat * l : ℕ) : ℤ) = (s - a * ρ) + (-(a * l)) * q := by
      push_cast; rw [hqn]; ring
    have hNq : (s - a * ((ρ + q.toNat * l : ℕ) : ℤ)) / q = (s - a * ρ) / q - a * l := by
      rw [hN, Int.add_mul_ediv_right _ _ hq.ne']; ring
    obtain ⟨r1, r2⟩ := floor_range hq hA hB
    rw [hNq] at r1 r2
    have hdec := level_decomp r1 r2
    have hn : 0 < n0 + ((ρ + q.toNat * l : ℕ) : ℤ) := by positivity
    have hm : n0 + (ρ : ℤ) + q * l = n0 + ((ρ + q.toNat * l : ℕ) : ℤ) := by push_cast; rw [hqn]; ring
    have i0 : ((s - a * ρ) / q - a * l ≤ G) ↔ ((s - a * ρ) / q - a * l) * (n0 + ρ + q * l) ≤ y := by
      rw [hm]; exact Int.le_ediv_iff_mul_le hn
    have i1 : ((s - a * ρ) / q - a * l + 1 ≤ G) ↔ ((s - a * ρ) / q + 1 - a * l) * (n0 + ρ + q * l) ≤ y := by
      rw [hm, show (s - a * ρ) / q + 1 - a * l = (s - a * ρ) / q - a * l + 1 by ring]
      exact Int.le_ediv_iff_mul_le hn
    have i2 : ((s - a * ρ) / q - a * l + 2 ≤ G) ↔ ((s - a * ρ) / q + 2 - a * l) * (n0 + ρ + q * l) ≤ y := by
      rw [hm, show (s - a * ρ) / q + 2 - a * l = (s - a * ρ) / q - a * l + 2 by ring]
      exact Int.le_ediv_iff_mul_le hn
    rw [if_congr i0 rfl rfl, if_congr i1 rfl rfl, if_congr i2 rfl rfl] at hdec
    rw [hdec]; ring
  -- non-exceptional classes have zero correction
  have hzero : ∀ ρ ∈ range q.toNat, (s - a * ρ) % q ∉ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ) →
      corr y n0 a q s k ρ = 0 := by
    intro ρ hρ hJ
    have hρ' := hρ
    rw [mem_range] at hρ'
    obtain ⟨j1, j2⟩ := notJ hq hinv (Int.emod_nonneg _ hq.ne') (Int.emod_lt_of_pos _ hq) hJ
    have := hrow ρ hρ
    have hlin : ∑ l ∈ range k, y / (n0 + ((ρ + q.toNat * l : ℕ) : ℤ))
        = ∑ l ∈ range k, ((s - a * ρ) / q - a * l) := by
      refine sum_congr rfl fun l hl => ?_
      rw [mem_range] at hl
      have htk : ρ + q.toNat * l < k * q.toNat := by nlinarith
      obtain ⟨hA, hB⟩ := hwin _ htk
      have hN : s - a * ((ρ + q.toNat * l : ℕ) : ℤ) = (s - a * ρ) + (-(a * l)) * q := by
        push_cast; rw [hqn]; ring
      have hNq : (s - a * ((ρ + q.toNat * l : ℕ) : ℤ)) / q = (s - a * ρ) / q - a * l := by
        rw [hN, Int.add_mul_ediv_right _ _ hq.ne']; ring
      have hNm : (s - a * ((ρ + q.toNat * l : ℕ) : ℤ)) % q = (s - a * ρ) % q := by
        rw [hN, Int.add_mul_emod_self_right]
      rw [← hNq]
      exact floor_eq_of_class hq hA hB (by rw [hNm]; exact j1) (by rw [hNm]; exact j2)
    linarith
  rw [sum_congr rfl hrow, sum_add_distrib]
  -- the corrections: only classes in J
  have hJsum : ∑ ρ ∈ range q.toNat, corr y n0 a q s k ρ
      = ∑ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ), corr y n0 a q s k (clsRho ainv s q j) := by
    rw [← sum_filter_of_ne (p := fun ρ : ℕ => (s - a * ρ) % q ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ))
      (fun ρ hρ hne => by by_contra hc; exact hne (hzero ρ hρ hc))]
    have hJmem : ∀ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ), 0 ≤ j ∧ j < q := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with h | h | h <;> subst h
      · exact ⟨le_rfl, hq⟩
      · exact ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩
      · exact ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩
    have himg : (range q.toNat).filter (fun ρ : ℕ => (s - a * ρ) % q ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ))
        = ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ).image (clsRho ainv s q) := by
      ext ρ
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hρ, hJ⟩
        exact ⟨_, hJ, cls_of_j hq hinv (by omega)⟩
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨j0, j1⟩ := hJmem j hj
        refine ⟨?_, by rw [j_of_cls hq hinv j0 j1]; exact hj⟩
        unfold clsRho
        have := Int.emod_lt_of_pos (ainv * (s - j)) hq
        have := Int.emod_nonneg (ainv * (s - j)) hq.ne'
        omega
    rw [himg, sum_image]
    intro j1 hj1 j2 hj2 h
    have e1 := j_of_cls (s := s) hq hinv (hJmem j1 hj1).1 (hJmem j1 hj1).2
    have e2 := j_of_cls (s := s) hq hinv (hJmem j2 hj2).1 (hJmem j2 hj2).2
    rw [← e1, ← e2, h]
  rw [hJsum]
  unfold blockFast
  rw [← hs_def]
  congr 1
  -- the linear part
  have hl : ∑ ρ ∈ range q.toNat, ∑ l ∈ range k, ((s - a * ρ) / q - a * l)
      = k * ∑ ρ ∈ range q.toNat, (s - a * ρ) / q - q * a * ∑ l ∈ range k, (l : ℤ) := by
    have : ∀ ρ ∈ range q.toNat, ∑ l ∈ range k, ((s - a * ρ) / q - a * l)
        = k * ((s - a * ρ) / q) - a * ∑ l ∈ range k, (l : ℤ) := by
      intro ρ _; rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
    rw [sum_congr rfl this, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hqn, ← mul_sum]
    ring
  rw [hl]
  have e1 := two_sum_floor (s := s) hq hinv
  have e2 := two_sum_range k
  rw [show 2 * (k : ℤ) * s - k * (a + 1) * (q - 1) - a * q * k * (k - 1)
      = 2 * (k * ∑ ρ ∈ range q.toNat, (s - a * ρ) / q - q * a * ∑ l ∈ range k, (l : ℤ)) by
    linear_combination (-(k : ℤ)) * e1 + q * a * e2]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-! ## Correctness of the loop and of `blockS` -/

lemma direct_eq_range (y n0 len : ℕ) :
    direct y n0 len = ∑ t ∈ range len, (y : ℤ) / ((n0 : ℤ) + (t : ℤ)) := by
  unfold direct
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine sum_congr rfl fun t _ => ?_
  push_cast; rfl

theorem blockStep_spec (y r n0 : ℕ) (h1 : 1 ≤ n0) (h2 : n0 ≤ r) :
    1 ≤ (blockStep y r n0).1 ∧ n0 + (blockStep y r n0).1 ≤ r + 1 ∧
    (blockStep y r n0).2 = direct y n0 (blockStep y r n0).1 := by
  unfold blockStep
  dsimp only
  set Q := icbrtF (n0 ^ 3 / y)
  set a := (approx y (n0 * n0) Q).1
  set q := (approx y (n0 * n0) Q).2
  split_ifs with hA hB
  · exact ⟨by omega, by omega, rfl⟩
  · push Not at hA
    obtain ⟨hq0, hqQ, hqR⟩ := hA
    have hk : 1 ≤ min Q (r + 1 - n0) / q := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have hH : min Q (r + 1 - n0) / q * q ≤ min Q (r + 1 - n0) := Nat.div_mul_le_self _ _
    dsimp only
    refine ⟨Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hq0), by omega, ?_⟩
    rw [direct_eq_range]
    have hqz : ((q : ℤ)).toNat = q := Int.toNat_natCast q
    have := blockFast_spec (y := (y : ℤ)) (n0 := (n0 : ℤ)) (a := (a : ℤ)) (q := (q : ℤ))
      (ainv := Nat.gcdA a q) (k := min Q (r + 1 - n0) / q) (by positivity) (by exact_mod_cast h1)
      (by positivity) (by exact_mod_cast (show 0 < q by omega)) hB.2.2
      (by rw [hqz]; exact hB.1) (by rw [hqz]; exact hB.2.1)
    rw [hqz] at this
    rw [this]
  · push Not at hA
    obtain ⟨hq0, hqQ, hqR⟩ := hA
    have hk : 1 ≤ min Q (r + 1 - n0) / q := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have hH : min Q (r + 1 - n0) / q * q ≤ min Q (r + 1 - n0) := Nat.div_mul_le_self _ _
    dsimp only
    exact ⟨Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hq0), by omega, rfl⟩

theorem loop_spec (y r : ℕ) : ∀ fuel n0 : ℕ, 1 ≤ n0 →
    loop y r fuel n0 = ∑ b ∈ Ico n0 (r + 1), ((y / b : ℕ) : ℤ)
  | 0, n0, _ => by
    unfold loop direct
    by_cases h : n0 ≤ r + 1
    · rw [Nat.add_sub_cancel' h]
    · rw [show r + 1 - n0 = 0 by omega, Nat.add_zero, Ico_self, Ico_eq_empty (by omega)]
  | fuel + 1, n0, hn0 => by
    unfold loop
    by_cases h : r < n0
    · rw [if_pos h, Ico_eq_empty (by omega), sum_empty]
    · rw [if_neg h]
      dsimp only
      obtain ⟨s1, s2, s3⟩ := blockStep_spec y r n0 hn0 (by omega)
      rw [loop_spec y r fuel _ (by omega), s3, direct, sum_Ico_consecutive _ (by omega) s2]

theorem blockSZ_eq (y L : ℕ) :
    blockSZ y L = ((∑ b ∈ Ioc L (Nat.sqrt y), y / b : ℕ) : ℤ) := by
  unfold blockSZ
  dsimp only
  rw [loop_spec y _ _ _ (by omega), direct, Nat.add_sub_cancel' (le_max_left _ _), Nat.cast_sum,
    ← Finset.Ico_add_one_add_one_eq_Ioc]
  set n1 := max (L + 1) (min (icbrtF y + 1) (Nat.sqrt y + 1))
  by_cases h : n1 ≤ Nat.sqrt y + 1
  · exact sum_Ico_consecutive _ (le_max_left _ _) h
  · rw [Ico_eq_empty (show ¬ n1 < Nat.sqrt y + 1 by omega), sum_empty, add_zero]
    have : n1 = L + 1 := by omega
    rw [this, Ico_self, Ico_eq_empty (by omega)]

/-- **Correctness of the block routine**: for all naturals `y` and `L`,
`blockS y L = ∑_{L < b ≤ isqrt y} floor(y / b)`. -/
theorem blockS_eq (y L : ℕ) : blockS y L = ∑ b ∈ Ioc L (Nat.sqrt y), y / b := by
  unfold blockS
  rw [blockSZ_eq, Int.toNat_natCast]

/-! ## `D3fast` via (F1) and the nested floor identity -/

/-- `B(x)` with the inner sums by the block routine. -/
def BsumF (x : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 (icbrtF x), ((blockS (x / a) (a - 1) : ℤ)
    - (((Nat.sqrt (x / a) : ℤ) * ((Nat.sqrt (x / a) : ℤ) - 1) - ((a : ℤ) - 1) * ((a : ℤ) - 2)) / 2))

def EabF (x : ℕ) : ℤ := ∑ a ∈ Icc 1 (icbrtF x), (((x / a ^ 2 : ℕ) : ℤ) - a + 1)

def EbcF (x : ℕ) : ℤ := ∑ a ∈ Icc 1 (icbrtF x), ((Nat.sqrt (x / a) : ℤ) - a + 1)

/-- `D_3(x) = 6 B - 3 E_ab - 3 E_bc + m`, computed with the block routine. -/
def D3fastZ (x : ℕ) : ℤ := 6 * BsumF x - 3 * EabF x - 3 * EbcF x + icbrtF x

/-- **The fast algorithm** for `D_3(x)`. -/
def D3fast (x : ℕ) : ℕ := (D3fastZ x).toNat

lemma two_sum_Icc_pred (a : ℕ) (ha : 1 ≤ a) : ∀ h : ℕ, a ≤ h + 1 →
    2 * ∑ b ∈ Icc a h, ((b : ℤ) - 1) = (h : ℤ) * ((h : ℤ) - 1) - ((a : ℤ) - 1) * ((a : ℤ) - 2) := by
  intro h hh
  induction h with
  | zero =>
    have : a = 1 := by omega
    subst this; simp
  | succ h ih =>
    by_cases hc : a ≤ h + 1
    · rw [sum_Icc_succ_top hc, mul_add, ih hc]; push_cast; ring
    · have : a = h + 2 := by omega
      subst this
      rw [Icc_eq_empty (by omega)]; push_cast; ring

lemma inner_eq (x a : ℕ) (ha : 1 ≤ a) (ham : a ≤ M2L3.icbrt x) :
    ∑ b ∈ Icc a (M2L3.ha x a), (((x / (a * b) : ℕ) : ℤ) - b + 1)
      = (blockS (x / a) (a - 1) : ℤ)
        - (((Nat.sqrt (x / a) : ℤ) * ((Nat.sqrt (x / a) : ℤ) - 1) - ((a : ℤ) - 1) * ((a : ℤ) - 2)) / 2) := by
  have hah : a ≤ M2L3.ha x a := (M2L3.a_le_ha_iff (by omega)).2 ham
  unfold M2L3.ha at hah ⊢
  rw [blockS_eq, ← two_sum_Icc_pred a ha _ (by omega), Int.mul_ediv_cancel_left _ (by norm_num)]
  have hI : Ioc (a - 1) (Nat.sqrt (x / a)) = Icc a (Nat.sqrt (x / a)) := by
    ext b; simp only [mem_Ioc, mem_Icc]; omega
  have hsum : ∑ b ∈ Icc a (Nat.sqrt (x / a)), x / a / b = ∑ b ∈ Icc a (Nat.sqrt (x / a)), x / (a * b) :=
    sum_congr rfl fun b _ => Nat.div_div_eq_div_mul x a b
  rw [hI, hsum, Nat.cast_sum]
  simp only [sum_add_distrib, sum_sub_distrib]
  ring

theorem BsumF_eq (x : ℕ) : BsumF x = M2L3.Bsum x := by
  unfold BsumF M2L3.Bsum
  rw [icbrtF_eq]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  exact (inner_eq x a ha.1 ha.2).symm

/-- **Correctness of `D3fast`**: for every natural `x`, `D3fast x = D_3(x)`. -/
theorem D3fast_eq (x : ℕ) : D3fast x = M2L3.D3 x := by
  have h : D3fastZ x = (M2L3.D3 x : ℤ) := by
    rw [M2L3.ternary_F1, D3fastZ, BsumF_eq, icbrtF_eq]
    unfold EabF EbcF M2L3.Eab M2L3.Ebc M2L3.ha
    rw [icbrtF_eq]
  unfold D3fast
  rw [h, Int.toNat_natCast]

/-- `π(x) mod 3` from the certified `D_3 mod 9` values (round 4 forward reduction). -/
def piMod3 (x : ℕ) : ZMod 3 := M2L4.piMod3OfD3 (fun y => D3fast y % 9) x

/-- **`piMod3 x = π(x) mod 3`** for every natural `x`. -/
theorem piMod3_correct (x : ℕ) : piMod3 x = (Nat.primeCounting x : ZMod 3) :=
  M2L4.piMod3OfD3_correct _ x fun y _ => by rw [D3fast_eq]

theorem piMod3_val (x : ℕ) : (piMod3 x).val = Nat.primeCounting x % 3 :=
  M2L4.piMod3OfD3_val _ x fun y _ => by rw [D3fast_eq]

end M2L5

/-! ## Evaluation (not used in any proof). Reference: D_3(10^6) = 106,030,594 (m2/e). -/
#eval M2L5.D3fast 1000000      -- 106030594
#eval M2L5.D3fast 10000000     -- 1421760251
#eval M2L5.D3fast 100000000    -- 18362473634
#eval (M2L5.piMod3 10000).val  -- 2 = π(10^4) mod 3 (π(10^4) = 1229)
