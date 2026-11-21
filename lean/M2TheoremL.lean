module

public import Mathlib
public import M2ResultM

/-!
  Seat M2L4, item 6: the elementary parts of Theorem L (A19 section 16).
  From the pointwise statements taken as hypotheses (W(1) = 1; 8 | W(n) when ω(n) ≥ 2;
  the prime-power values (N2)), the summed mod 8 formula and (N3), for every x ≥ 1, with the
  correction C_R written through prime counts at integer roots ⌊x^(1/j)⌋, 2 ≤ j ≤ ⌊log₂ x⌋.
  Also the elementary pointwise part: the sign-change argument 4 | r*(n) for n > 1 coprime to 6,
  hence 8 | W(n) when ω(n) ≥ 2, and W(1) = 1, for W defined from r* as in (N1).
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.omega

namespace M2L4
open M2L3

/-! ## Prime-power decomposition of a prefix sum -/

lemma ppow_pointwise (W : ℕ → ℤ) {x n : ℕ} (hn : n ∈ Ioc 0 x) :
    (if IsPrimePow n then W n else 0)
      = ∑ k ∈ Ioc 0 x, ∑ p ∈ Ioc 0 x, (if p ^ k = n ∧ p.Prime then W (p ^ k) else 0) := by
  rw [mem_Ioc] at hn
  by_cases hpp : IsPrimePow n
  · rw [ite_eq_left hpp]
    obtain ⟨p0, k0, hp0, hk0, rfl⟩ := hpp
    rw [← Nat.prime_iff] at hp0
    have hk0x : k0 ∈ Ioc 0 x := mem_Ioc.2 ⟨hk0, (Nat.lt_pow_self hp0.one_lt).le.trans hn.2⟩
    have hp0x : p0 ∈ Ioc 0 x :=
      mem_Ioc.2 ⟨hp0.pos, (Nat.le_self_pow hk0.ne' p0).trans hn.2⟩
    rw [sum_eq_single_of_mem k0 hk0x, sum_eq_single_of_mem p0 hp0x, ite_eq_left ⟨rfl, hp0⟩]
    · intro p _ hp
      rw [ite_eq_right]
      rintro ⟨h, hpr⟩
      exact hp (hpr.pow_inj' hp0 hk0.ne' hk0.ne' h).1
    · intro k hk hkk
      apply sum_eq_zero
      intro p _
      rw [ite_eq_right]
      rintro ⟨h, hpr⟩
      exact hkk (hpr.pow_inj' hp0 (mem_Ioc.1 hk).1.ne' hk0.ne' h).2
  · rw [ite_eq_right hpp]
    symm
    apply sum_eq_zero; intro k hk
    apply sum_eq_zero; intro p _
    rw [ite_eq_right]
    rintro ⟨h, hpr⟩
    exact hpp ⟨p, k, Nat.prime_iff.1 hpr, (mem_Ioc.1 hk).1, h⟩

/-- `∑_{n ≤ x, n a prime power} W(n) = ∑_{1 ≤ k ≤ x} ∑_{p prime, p^k ≤ x} W(p^k)`. -/
theorem sum_primePow (W : ℕ → ℤ) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if IsPrimePow n then W n else 0)
      = ∑ k ∈ Ioc 0 x, ∑ p ∈ (Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x), W (p ^ k) := by
  rw [sum_congr rfl fun n hn => ppow_pointwise W hn, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun p hp => ?_
  simp only [ite_and]
  rw [sum_ite_eq]
  have hp0 : 0 < p := (mem_Ioc.1 hp).1
  have hpk : 0 < p ^ k := pow_pos hp0 k
  by_cases hpr : p.Prime <;> by_cases hle : p ^ k ≤ x <;> simp [hpr, hle, mem_Ioc, hpk]

/-- `ω(n) = 0` iff `n ≤ 1`; `ω(n) = 1` iff `n` is a prime power. -/
lemma omega_cases {n : ℕ} (hn : 0 < n) : n = 1 ∨ IsPrimePow n ∨ 2 ≤ ω n := by
  by_cases h1 : n = 1
  · exact Or.inl h1
  · right
    by_cases hpp : IsPrimePow n
    · exact Or.inl hpp
    · right
      have h0 : ω n ≠ 0 := by rw [Ne, cardDistinctFactors_eq_zero]; omega
      have h1' : ω n ≠ 1 := fun h => hpp (cardDistinctFactors_eq_one_iff.1 h)
      omega

/-! ## The summed mod 8 formula and (N3) -/

section Summed

variable (R : ℕ → Prop) [DecidablePred R]

/-- `π_R(y) = #{q ≤ y : q ∈ R}`. -/
def piR (y : ℕ) : ℕ := ((Ioc 0 y).filter R).card

/-- `π_+(y) = #{q ≤ y prime : q > 3, q ≡ 1 (mod 3)}`. -/
def piPlus (y : ℕ) : ℕ := ((Ioc 0 y).filter (fun q => q.Prime ∧ 3 < q ∧ q % 3 = 1)).card

/-- `C_R(x) = ∑_{2 ≤ j ≤ ⌊log₂ x⌋} (π_+(⌊x^(1/j)⌋) if 3 ∣ j, else π_R(⌊x^(1/j)⌋))`. -/
def CR (x : ℕ) : ℤ :=
  ∑ j ∈ Icc 2 (Nat.log 2 x), (if 3 ∣ j then (piPlus (iroot j x) : ℤ) else piR R (iroot j x))

/-- The count at exponent `k`: primes `q` with `q^k ≤ x`, `q > 3`, `q ≡ 1 (3)`, `q ∈ R or 3 ∣ k`. -/
def cnt (k x : ℕ) : ℕ :=
  ((Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x ∧ (3 < p ∧ p % 3 = 1 ∧ (R p ∨ 3 ∣ k)))).card

variable {R}

lemma cnt_eq_zero {k x : ℕ} (h : x < 2 ^ k) : cnt R k x = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro p - ⟨hp, hpk, -⟩
  have := Nat.pow_le_pow_left hp.two_le k
  omega

lemma cnt_eq (hR : ∀ q, R q → q.Prime ∧ 3 < q ∧ q % 3 = 1) {k : ℕ} (hk : 0 < k) (x : ℕ) :
    cnt R k x = if 3 ∣ k then piPlus (iroot k x) else piR R (iroot k x) := by
  unfold cnt piPlus piR
  split_ifs with h3
  · congr 1; ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h0, -⟩, hp, hpk, h3', h1, -⟩
      exact ⟨⟨h0, (pow_le_iff_le_iroot hk).1 hpk⟩, hp, h3', h1⟩
    · rintro ⟨⟨h0, hle⟩, hp, h3', h1⟩
      have hpk := (pow_le_iff_le_iroot hk).2 hle
      exact ⟨⟨h0, le_of_pow_le' hk hpk⟩, hp, hpk, h3', h1, Or.inr h3⟩
  · congr 1; ext p
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨h0, -⟩, hp, hpk, h3', h1, hr⟩
      exact ⟨⟨h0, (pow_le_iff_le_iroot hk).1 hpk⟩, hr.resolve_right h3⟩
    · rintro ⟨⟨h0, hle⟩, hr⟩
      have hpk := (pow_le_iff_le_iroot hk).2 hle
      obtain ⟨hp, h3', h1⟩ := hR p hr
      exact ⟨⟨h0, le_of_pow_le' hk hpk⟩, hp, hpk, h3', h1, Or.inl hr⟩

/-- **Summed form of Theorem L**, exact up to the composite part: from the pointwise hypotheses,
for every `x ≥ 1`,
`∑_{n ≤ x} W(n) = 1 + 4 (π_R(x) + C_R(x)) + ∑_{n ≤ x, ω(n) ≥ 2} W(n)`. -/
theorem L_summed_exact (W : ℕ → ℤ) (hR : ∀ q, R q → q.Prime ∧ 3 < q ∧ q % 3 = 1)
    (hW1 : W 1 = 1)
    (hWpp : ∀ q j, q.Prime → 1 ≤ j →
      W (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ (R q ∨ 3 ∣ j) then 4 else 0)
    {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, W n
      = 1 + 4 * ((piR R x : ℤ) + CR R x) + ∑ n ∈ (Ioc 0 x).filter (fun n => 2 ≤ ω n), W n := by
  -- split each term by `n = 1`, prime power, `ω ≥ 2`
  have hsplit : ∀ n ∈ Ioc 0 x, W n = (if n = 1 then W n else 0) + (if IsPrimePow n then W n else 0)
      + (if 2 ≤ ω n then W n else 0) := by
    intro n hn
    rcases omega_cases (mem_Ioc.1 hn).1 with h | h | h
    · subst h; simp [not_isPrimePow_one]
    · have h1 : n ≠ 1 := fun e => not_isPrimePow_one (e ▸ h)
      have h2 : ¬ 2 ≤ ω n := by rw [cardDistinctFactors_eq_one_iff.2 h]; omega
      simp [h1, h, h2]
    · have h1 : n ≠ 1 := by rintro rfl; simp at h
      have h2 : ¬ IsPrimePow n := fun hp => by rw [cardDistinctFactors_eq_one_iff.2 hp] at h; omega
      simp [h1, h2, h]
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, sum_ite_eq', ite_eq_left (by simp; omega),
    hW1, sum_primePow, ← sum_filter]
  congr 1
  -- the prime-power part
  have hk : ∀ k ∈ Ioc 0 x, ∑ p ∈ (Ioc 0 x).filter (fun p => p.Prime ∧ p ^ k ≤ x), W (p ^ k)
      = 4 * (cnt R k x : ℤ) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Ioc.1 hk).1
    rw [sum_congr rfl fun p hp => hWpp p k (mem_filter.1 hp).2.1 hk1, ← sum_filter, sum_const,
      nsmul_eq_mul, mul_comm, cnt, filter_filter]
    congr 3
    ext p; simp only [mem_filter, and_assoc]
  rw [sum_congr rfl hk, ← mul_sum]
  -- trim to `1 ≤ k ≤ ⌊log₂ x⌋` and identify the counts
  have hN := lt_two_pow_log x
  have hz : ∀ k, min x (Nat.log 2 x) < k → 4 * (cnt R k x : ℤ) = 0 := by
    intro k hk'
    rw [cnt_eq_zero, Nat.cast_zero, mul_zero]
    rcases min_lt_iff.1 hk' with h | h
    · exact lt_of_le_of_lt (Nat.lt_two_pow_self).le (Nat.pow_lt_pow_right (by norm_num) h)
    · exact lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) h)
  have htrim : ∑ k ∈ Ioc 0 x, 4 * (cnt R k x : ℤ) = ∑ k ∈ Ioc 0 (Nat.log 2 x), 4 * (cnt R k x : ℤ) := by
    rw [sum_Ioc_trim _ (min_le_left x _) hz, sum_Ioc_trim _ (min_le_right x _) hz]
  rw [mul_sum, htrim, ← mul_sum]
  congr 2
  have hlog : 1 ≤ Nat.log 2 x ∨ Nat.log 2 x = 0 := by omega
  rcases hlog with hl | hl
  · have hs : Ioc 0 (Nat.log 2 x) = insert 1 (Icc 2 (Nat.log 2 x)) := by
      ext k; simp only [mem_Ioc, mem_insert, mem_Icc]; omega
    rw [hs, sum_insert (by simp), CR]
    congr 1
    · rw [cnt_eq hR one_pos, ite_eq_right (by norm_num), iroot_one]
    · refine sum_congr rfl fun k hk => ?_
      rw [cnt_eq hR (by have := (mem_Icc.1 hk).1; omega)]
      split_ifs <;> rfl
  · have hx1 : x = 1 := by have := lt_two_pow_log x; rw [hl] at this; omega
    subst hx1
    rw [hl, CR, hl]
    have h1 : ¬ R 1 := fun h => (hR 1 h).1.ne_one rfl
    have hf : ({1} : Finset ℕ).filter R = ∅ := by rw [filter_singleton, ite_eq_right h1]
    simp [piR, hf]

/-- **The summed mod 8 formula of Theorem L**: for every `x ≥ 1`,
`∑_{n ≤ x} W(n) ≡ 1 + 4 (π_R(x) + C_R(x)) (mod 8)`. -/
theorem L_summed_mod8 (W : ℕ → ℤ) (hR : ∀ q, R q → q.Prime ∧ 3 < q ∧ q % 3 = 1)
    (hW1 : W 1 = 1) (hW2 : ∀ n, 2 ≤ ω n → 8 ∣ W n)
    (hWpp : ∀ q j, q.Prime → 1 ≤ j →
      W (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ (R q ∨ 3 ∣ j) then 4 else 0)
    {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, W n ≡ 1 + 4 * ((piR R x : ℤ) + CR R x) [ZMOD 8] := by
  rw [L_summed_exact W hR hW1 hWpp hx, Int.modEq_iff_dvd]
  have : (8 : ℤ) ∣ ∑ n ∈ (Ioc 0 x).filter (fun n => 2 ≤ ω n), W n :=
    dvd_sum fun n hn => hW2 n (mem_filter.1 hn).2
  rw [show 1 + 4 * ((piR R x : ℤ) + CR R x) - (1 + 4 * ((piR R x : ℤ) + CR R x)
    + ∑ n ∈ (Ioc 0 x).filter (fun n => 2 ≤ ω n), W n)
    = -∑ n ∈ (Ioc 0 x).filter (fun n => 2 ≤ ω n), W n by ring]
  exact this.neg_right

/-- **(N3)**: for every `x ≥ 1`, `4 ∣ ∑_{n ≤ x} W(n) - 1` exactly, and
`π_R(x) ≡ (∑_{n ≤ x} W(n) - 1)/4 - C_R(x) (mod 2)`. -/
theorem L_N3 (W : ℕ → ℤ) (hR : ∀ q, R q → q.Prime ∧ 3 < q ∧ q % 3 = 1)
    (hW1 : W 1 = 1) (hW2 : ∀ n, 2 ≤ ω n → 8 ∣ W n)
    (hWpp : ∀ q j, q.Prime → 1 ≤ j →
      W (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ (R q ∨ 3 ∣ j) then 4 else 0)
    {x : ℕ} (hx : 1 ≤ x) :
    (4 : ℤ) ∣ ∑ n ∈ Ioc 0 x, W n - 1 ∧
      (piR R x : ℤ) ≡ (∑ n ∈ Ioc 0 x, W n - 1) / 4 - CR R x [ZMOD 2] := by
  have hE := L_summed_exact W hR hW1 hWpp hx
  obtain ⟨K, hK⟩ : (8 : ℤ) ∣ ∑ n ∈ (Ioc 0 x).filter (fun n => 2 ≤ ω n), W n :=
    dvd_sum fun n hn => hW2 n (mem_filter.1 hn).2
  have e : ∑ n ∈ Ioc 0 x, W n - 1 = 4 * ((piR R x : ℤ) + CR R x + 2 * K) := by
    rw [hE, hK]; ring
  refine ⟨⟨_, e⟩, ?_⟩
  rw [e, Int.mul_ediv_cancel_left _ (by norm_num), Int.modEq_iff_dvd]
  exact ⟨K, by ring⟩

end Summed

/-! ## The elementary pointwise part of (N1) -/

section Pointwise

/-- `r*(n) = #{(a, b) ∈ ℤ² : a² + 27 b² = n, gcd(a, b) = 1}` (the box `|a|, |b| ≤ n` contains all). -/
noncomputable def rStar (n : ℕ) : ℕ :=
  ((Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter
    (fun ab : ℤ × ℤ => ab.1 ^ 2 + 27 * ab.2 ^ 2 = n ∧ Int.gcd ab.1 ab.2 = 1)).card

/-- `W(n) = 2^ω(n) r*(n) / 2` for `(n, 6) = 1`, `0` otherwise (equation (N1)). -/
noncomputable def Wfun (n : ℕ) : ℤ := if Nat.Coprime n 6 then 2 ^ ω n * (rStar n : ℤ) / 2 else 0

/-- `r*(1) = 2`. -/
theorem rStar_one : rStar 1 = 2 := by decide

theorem Wfun_one : Wfun 1 = 1 := by
  rw [Wfun, ite_eq_left (by norm_num), rStar_one]; simp

/-- For `n > 1` coprime to 6 every primitive representation has both coordinates nonzero, so the
independent sign changes act freely: `4 ∣ r*(n)`. -/
theorem four_dvd_rStar {n : ℕ} (hn : 1 < n) (h6 : Nat.Coprime n 6) : 4 ∣ rStar n := by
  set S := (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter
    (fun ab : ℤ × ℤ => ab.1 ^ 2 + 27 * ab.2 ^ 2 = n ∧ Int.gcd ab.1 ab.2 = 1) with hS
  have hmem : ∀ a b : ℤ, (a, b) ∈ S ↔ a ^ 2 + 27 * b ^ 2 = n ∧ Int.gcd a b = 1 := by
    intro a b
    simp only [hS, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨h1, h2⟩
      have ha : a ^ 2 ≤ n := by nlinarith
      have hb : b ^ 2 ≤ n := by nlinarith
      have ha' : |a| ≤ n := by
        have : |a| ≤ a ^ 2 := by
          rcases eq_or_ne a 0 with rfl | h0
          · simp
          · have := Int.one_le_abs h0; nlinarith [sq_abs a]
        linarith
      have hb' : |b| ≤ n := by
        have : |b| ≤ b ^ 2 := by
          rcases eq_or_ne b 0 with rfl | h0
          · simp
          · have := Int.one_le_abs h0; nlinarith [sq_abs b]
        linarith
      exact ⟨⟨abs_le.1 ha', abs_le.1 hb'⟩, h1, h2⟩
  -- both coordinates are nonzero on `S`
  have hnz : ∀ ab ∈ S, ab.1 ≠ 0 ∧ ab.2 ≠ 0 := by
    rintro ⟨a, b⟩ hab
    obtain ⟨h1, h2⟩ := (hmem a b).1 hab
    constructor
    · rintro rfl
      simp at h2
      have : (n : ℤ) = 27 * b ^ 2 := by rw [← h1]; ring
      have hb : b ^ 2 = 1 := by
        rcases Int.natAbs_eq b with h | h <;> rw [h] <;> simp [h2]
      rw [hb] at this
      have : n = 27 := by exact_mod_cast this
      subst this; norm_num at h6
    · rintro rfl
      simp at h2
      have hb : a ^ 2 = 1 := by
        rcases Int.natAbs_eq a with h | h <;> rw [h] <;> simp [h2]
      rw [hb] at h1
      have : n = 1 := by
        have : (1 : ℤ) + 27 * 0 ^ 2 = n := h1
        exact_mod_cast (by simpa using this.symm : (n : ℤ) = 1)
      omega
  -- `S` is the disjoint union of four sign images of its positive quadrant
  set Q := S.filter (fun ab => 0 < ab.1 ∧ 0 < ab.2) with hQ
  have himg : S = Q.image (fun ab => ab) ∪ Q.image (fun ab => (-ab.1, ab.2)) ∪
      Q.image (fun ab => (ab.1, -ab.2)) ∪ Q.image (fun ab => (-ab.1, -ab.2)) := by
    ext ⟨a, b⟩
    simp only [hQ, mem_union, mem_image, mem_filter, Prod.mk.injEq, Prod.exists]
    constructor
    · intro hab
      obtain ⟨ha, hb⟩ := hnz _ hab
      obtain ⟨h1, h2⟩ := (hmem a b).1 hab
      rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
      · right; exact ⟨-a, -b, ⟨(hmem _ _).2 ⟨by rw [← h1]; ring, by simpa using h2⟩, by omega,
          by omega⟩, by ring, by ring⟩
      · left; left; right; exact ⟨-a, b, ⟨(hmem _ _).2 ⟨by rw [← h1]; ring, by simpa using h2⟩,
          by omega, hb⟩, by ring, rfl⟩
      · left; right; exact ⟨a, -b, ⟨(hmem _ _).2 ⟨by rw [← h1]; ring, by simpa using h2⟩,
          ha, by omega⟩, rfl, by ring⟩
      · left; left; left; exact ⟨a, b, ⟨hab, ha, hb⟩, rfl, rfl⟩
    · rintro (((⟨a', b', ⟨h, -⟩, rfl, rfl⟩ | ⟨a', b', ⟨h, -⟩, rfl, rfl⟩) |
        ⟨a', b', ⟨h, -⟩, rfl, rfl⟩) | ⟨a', b', ⟨h, -⟩, rfl, rfl⟩)
      · exact h
      · obtain ⟨h1, h2⟩ := (hmem a' b').1 h
        exact (hmem _ _).2 ⟨by rw [← h1]; ring, by simpa using h2⟩
      · obtain ⟨h1, h2⟩ := (hmem a' b').1 h
        exact (hmem _ _).2 ⟨by rw [← h1]; ring, by simpa using h2⟩
      · obtain ⟨h1, h2⟩ := (hmem a' b').1 h
        exact (hmem _ _).2 ⟨by rw [← h1]; ring, by simpa using h2⟩
  have hinj : ∀ (f : ℤ × ℤ → ℤ × ℤ), Function.Injective f → (Q.image f).card = Q.card :=
    fun f hf => card_image_of_injective _ hf
  have i1 : Function.Injective (fun ab : ℤ × ℤ => ab) := fun _ _ h => h
  have i2 : Function.Injective (fun ab : ℤ × ℤ => (-ab.1, ab.2)) := by
    intro x y h; simp only [Prod.mk.injEq, neg_inj] at h; exact Prod.ext h.1 h.2
  have i3 : Function.Injective (fun ab : ℤ × ℤ => (ab.1, -ab.2)) := by
    intro x y h; simp only [Prod.mk.injEq, neg_inj] at h; exact Prod.ext h.1 h.2
  have i4 : Function.Injective (fun ab : ℤ × ℤ => (-ab.1, -ab.2)) := by
    intro x y h; simp only [Prod.mk.injEq, neg_inj] at h; exact Prod.ext h.1 h.2
  have hdisj : ∀ (f g : ℤ × ℤ → ℤ × ℤ) (s1 s2 : ℤ → Prop),
      (∀ x ∈ Q, s1 (f x).1 ∧ s2 (f x).2) → (∀ x ∈ Q, ¬ (s1 (g x).1 ∧ s2 (g x).2)) →
      Disjoint (Q.image f) (Q.image g) := by
    intro f g s1 s2 hf hg
    rw [disjoint_left]
    intro y hy1 hy2
    obtain ⟨x1, hx1, rfl⟩ := mem_image.1 hy1
    obtain ⟨x2, hx2, he⟩ := mem_image.1 hy2
    exact hg x2 hx2 (he ▸ hf x1 hx1)
  have pos : ∀ x ∈ Q, 0 < x.1 ∧ 0 < x.2 := fun x hx => (mem_filter.1 hx).2
  have hc : rStar n = 4 * Q.card := by
    show S.card = _
    rw [himg, card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint,
      hinj _ i1, hinj _ i2, hinj _ i3, hinj _ i4]
    · ring
    · exact hdisj _ _ (fun t => 0 < t) (fun t => 0 < t) (fun x hx => pos x hx)
        (fun x hx h => by have := pos x hx; simp at h; omega)
    · rw [disjoint_union_left]
      exact ⟨hdisj _ _ (fun t => 0 < t) (fun t => 0 < t) (fun x hx => pos x hx)
          (fun x hx h => by have := pos x hx; simp at h; omega),
        hdisj _ _ (fun t => t < 0) (fun t => 0 < t) (fun x hx => by have := pos x hx; simp; omega)
          (fun x hx h => by have := pos x hx; simp at h; omega)⟩
    · rw [disjoint_union_left, disjoint_union_left]
      exact ⟨⟨hdisj _ _ (fun t => 0 < t) (fun t => 0 < t) (fun x hx => pos x hx)
          (fun x hx h => by have := pos x hx; simp at h; omega),
        hdisj _ _ (fun t => t < 0) (fun t => 0 < t) (fun x hx => by have := pos x hx; simp; omega)
          (fun x hx h => by have := pos x hx; simp at h; omega)⟩,
        hdisj _ _ (fun t => 0 < t) (fun t => t < 0) (fun x hx => by have := pos x hx; simp; omega)
          (fun x hx h => by have := pos x hx; simp at h; omega)⟩
  exact ⟨Q.card, hc⟩

/-- **(N1) pointwise, elementary part**: `8 ∣ W(n)` whenever `ω(n) ≥ 2`. -/
theorem Wfun_eight_dvd {n : ℕ} (hn : 2 ≤ ω n) : (8 : ℤ) ∣ Wfun n := by
  unfold Wfun
  split_ifs with h6
  · have hn1 : 1 < n := by
      by_contra h; push Not at h
      interval_cases n <;> simp at hn
    obtain ⟨t, ht⟩ := four_dvd_rStar hn1 h6
    obtain ⟨w, hw⟩ : ∃ w, ω n = w + 2 := ⟨ω n - 2, by omega⟩
    rw [ht, hw]
    push_cast
    rw [show (2 : ℤ) ^ (w + 2) * (4 * t) = 2 * (2 ^ w * 8 * t) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact ⟨2 ^ w * t, by ring⟩
  · exact dvd_zero _

end Pointwise

end M2L4
