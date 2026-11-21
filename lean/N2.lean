module

public import Mathlib
public import M2TheoremL
import all M2TheoremL

/-!
  Seat M2L6n: (N2) for `Wfun` and `R = R27` (primes of the form a^2 + 27 b^2).
  (a) `Wfun (q^j) = 0` for primes `q ≡ 2 (mod 3)`.
  (b) `Wfun (q^j) ∈ {0, 4}` for primes `q > 3` (uniqueness of primitive representations).
  (c) the exact value `Wfun_prime_pow`, in the form of the hypothesis `hWpp` of M2TheoremL,
      and the unconditional Theorem L statements.
  Route: elementary. Uniqueness from (ad - bc)(ad + bc) = N (d^2 - b^2) and
  N^2 = (ac ± k bd)^2 + k (ad ∓ bc)^2; Fermat for x^2 + 3y^2 by Thue's lemma (pigeonhole);
  existence and the criterion from powers of x + y√-3 in `ℤ√(-3)` (primitive by an ideal
  argument) and their imaginary parts mod 3.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.omega

@[expose] public section

namespace M2L6n
open M2L4

/-- membership in the set counted by `rStar`. -/
lemma mem_rStarSet (n : ℕ) (a b : ℤ) :
    (a, b) ∈ (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter
      (fun ab : ℤ × ℤ => ab.1 ^ 2 + 27 * ab.2 ^ 2 = n ∧ Int.gcd ab.1 ab.2 = 1)
      ↔ a ^ 2 + 27 * b ^ 2 = n ∧ Int.gcd a b = 1 := by
  simp only [mem_filter, mem_product, mem_Icc]
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

/-- For a prime `q > 3`, `Wfun (q^j) = rStar (q^j)`. -/
lemma Wfun_prime_pow_eq_rStar {q j : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hj : 1 ≤ j) :
    Wfun (q ^ j) = rStar (q ^ j) := by
  have hc : Nat.Coprime (q ^ j) 6 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases q <;> simp_all (config := { decide := true })
  rw [Wfun, ite_eq_left hc, cardDistinctFactors_apply_prime_pow hq (by omega)]
  simp

/-- A prime `q` does not divide either coordinate of a primitive representation
`a^2 + k b^2 = q^j` (`j ≥ 1`) when `q ∤ k`. -/
lemma not_dvd_fst {q : ℕ} (hq : q.Prime) {k a b : ℤ} {j : ℕ} (hj : 1 ≤ j)
    (hk : ¬ (q : ℤ) ∣ k) (h : a ^ 2 + k * b ^ 2 = (q : ℤ) ^ j) (hg : Int.gcd a b = 1) :
    ¬ (q : ℤ) ∣ a := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  intro ha
  have h1 : (q : ℤ) ∣ k * b ^ 2 := by
    have : (q : ℤ) ∣ (q : ℤ) ^ j := dvd_pow_self _ (by omega)
    rw [← h] at this
    exact (dvd_add_right (dvd_pow ha (by norm_num))).1 this
  have hb : (q : ℤ) ∣ b := hp.dvd_of_dvd_pow ((hp.dvd_or_dvd h1).resolve_left hk)
  have : (q : ℤ) ∣ (Int.gcd a b : ℤ) := Int.dvd_coe_gcd ha hb
  rw [hg] at this
  exact hp.not_isUnit (isUnit_of_dvd_one this)

lemma not_dvd_snd {q : ℕ} (hq : q.Prime) {k a b : ℤ} {j : ℕ} (hj : 1 ≤ j)
    (_hk : ¬ (q : ℤ) ∣ k) (h : a ^ 2 + k * b ^ 2 = (q : ℤ) ^ j) (hg : Int.gcd a b = 1) :
    ¬ (q : ℤ) ∣ b := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  intro hb
  have h1 : (q : ℤ) ∣ a ^ 2 := by
    have : (q : ℤ) ∣ (q : ℤ) ^ j := dvd_pow_self _ (by omega)
    rw [← h] at this
    exact (dvd_add_left (dvd_mul_of_dvd_right (dvd_pow hb (by norm_num)) _)).1 this
  have ha : (q : ℤ) ∣ a := hp.dvd_of_dvd_pow h1
  have : (q : ℤ) ∣ (Int.gcd a b : ℤ) := Int.dvd_coe_gcd ha hb
  rw [hg] at this
  exact hp.not_isUnit (isUnit_of_dvd_one this)

/-- mutual divisibility gives equal squares. -/
lemma sq_eq_of_dvd_dvd {a c : ℤ} (h1 : a ∣ c) (h2 : c ∣ a) : a ^ 2 = c ^ 2 := by
  rw [← Int.natAbs_eq_iff_sq_eq]
  exact Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.2 h1) (Int.natAbs_dvd_natAbs.2 h2)

/-- **Uniqueness of primitive representations** of an odd prime power by `x^2 + k y^2`
(`k ≥ 2`, `q ∤ k`): any two agree up to signs. -/
theorem prim_rep_unique {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {k : ℤ} (hk2 : 2 ≤ k)
    (hk : ¬ (q : ℤ) ∣ k) {j : ℕ} (hj : 1 ≤ j) {a b c d : ℤ}
    (h1 : a ^ 2 + k * b ^ 2 = (q : ℤ) ^ j) (g1 : Int.gcd a b = 1)
    (h2 : c ^ 2 + k * d ^ 2 = (q : ℤ) ^ j) (g2 : Int.gcd c d = 1) :
    a ^ 2 = c ^ 2 ∧ b ^ 2 = d ^ 2 := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  set N : ℤ := (q : ℤ) ^ j with hN
  have hN0 : 0 < N := pow_pos (by exact_mod_cast hq.pos) _
  have ha := not_dvd_fst hq hj hk h1 g1
  have hd := not_dvd_snd hq hj hk h2 g2
  have key : (a * d - b * c) * (a * d + b * c) = N * (d ^ 2 - b ^ 2) := by
    linear_combination d ^ 2 * h1 - b ^ 2 * h2
  have hdiv : (q : ℤ) ^ j ∣ (a * d - b * c) * (a * d + b * c) := ⟨_, key⟩
  have hnot : ¬ ((q : ℤ) ∣ a * d - b * c ∧ (q : ℤ) ∣ a * d + b * c) := by
    rintro ⟨u, v⟩
    have h2ad : (q : ℤ) ∣ 2 * (a * d) := by
      have := dvd_add u v; rw [show a * d - b * c + (a * d + b * c) = 2 * (a * d) by ring] at this
      exact this
    rcases hp.dvd_or_dvd h2ad with h | h
    · have : (q : ℕ) ∣ 2 := by exact_mod_cast h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
    · rcases hp.dvd_or_dvd h with h | h
      · exact ha h
      · exact hd h
  have hcop1 : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.2 g1
  have hcop2 : IsCoprime c d := Int.isCoprime_iff_gcd_eq_one.2 g2
  -- `a ∣ c` and `c ∣ a` in both cases
  have hac : a ∣ c ∧ c ∣ a := by
    by_cases hm : (q : ℤ) ∣ a * d + b * c
    · have hp' : (q : ℤ) ^ j ∣ a * d + b * c :=
        hp.pow_dvd_of_dvd_mul_left j (fun h => hnot ⟨h, hm⟩) hdiv
      obtain ⟨t, ht⟩ := hp'
      have iden : N ^ 2 = (a * c - k * b * d) ^ 2 + k * (a * d + b * c) ^ 2 := by
        rw [show N ^ 2 = N * N by ring]
        nth_rewrite 1 [← h1]; rw [← h2]; ring
      have ht0 : t = 0 := by
        by_contra ht0
        have : 1 ≤ t ^ 2 := by have := Int.one_le_abs ht0; nlinarith [sq_abs t]
        rw [ht] at iden
        nlinarith [sq_nonneg (a * c - k * b * d), sq_nonneg N]
      rw [ht0, mul_zero] at ht
      have e : a * d = -(b * c) := by linarith
      have x1 : a ∣ c * b := ⟨-d, by linear_combination e⟩
      have x2 : c ∣ a * d := ⟨-b, by linear_combination e⟩
      exact ⟨hcop1.dvd_of_dvd_mul_right x1, hcop2.dvd_of_dvd_mul_right x2⟩
    · have hp' : (q : ℤ) ^ j ∣ a * d - b * c := by
        rw [mul_comm] at hdiv
        exact hp.pow_dvd_of_dvd_mul_left j hm hdiv
      obtain ⟨t, ht⟩ := hp'
      have iden : N ^ 2 = (a * c + k * b * d) ^ 2 + k * (a * d - b * c) ^ 2 := by
        rw [show N ^ 2 = N * N by ring]
        nth_rewrite 1 [← h1]; rw [← h2]; ring
      have ht0 : t = 0 := by
        by_contra ht0
        have : 1 ≤ t ^ 2 := by have := Int.one_le_abs ht0; nlinarith [sq_abs t]
        rw [ht] at iden
        nlinarith [sq_nonneg (a * c + k * b * d), sq_nonneg N]
      rw [ht0, mul_zero] at ht
      have e : a * d = b * c := by linarith
      have x1 : a ∣ c * b := ⟨d, by linear_combination -e⟩
      have x2 : c ∣ a * d := ⟨b, by linear_combination e⟩
      exact ⟨hcop1.dvd_of_dvd_mul_right x1, hcop2.dvd_of_dvd_mul_right x2⟩
  have hsq := sq_eq_of_dvd_dvd hac.1 hac.2
  refine ⟨hsq, ?_⟩
  have : k * b ^ 2 = k * d ^ 2 := by linarith
  exact mul_left_cancel₀ (by positivity) this


/-! ## Counting: `rStar (q^j)` is `4` or `0` -/

lemma rep_of_sq_eq {N A B c d : ℤ} (h : A ^ 2 + 27 * B ^ 2 = N) (g : Int.gcd A B = 1)
    (e1 : c ^ 2 = A ^ 2) (e2 : d ^ 2 = B ^ 2) : c ^ 2 + 27 * d ^ 2 = N ∧ Int.gcd c d = 1 := by
  refine ⟨by rw [e1, e2, h], ?_⟩
  rw [Int.gcd_eq_natAbs, Int.natAbs_eq_iff_sq_eq.2 e1, Int.natAbs_eq_iff_sq_eq.2 e2,
    ← Int.gcd_eq_natAbs, g]

lemma not_dvd_27 {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) : ¬ (q : ℤ) ∣ 27 := by
  intro h
  have h' : q ∣ 3 ^ 3 := by exact_mod_cast h
  have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h')
  omega

open Classical in
/-- `rStar (q^j)` is `4` if `q^j` has a primitive representation by `x^2 + 27 y^2`, else `0`. -/
theorem rStar_prime_pow {q j : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hj : 1 ≤ j) :
    rStar (q ^ j) = if (∃ a b : ℤ, a ^ 2 + 27 * b ^ 2 = ((q ^ j : ℕ) : ℤ) ∧ Int.gcd a b = 1)
      then 4 else 0 := by
  have hq2 : q ≠ 2 := by omega
  have h27 := not_dvd_27 hq hq3
  unfold rStar
  split_ifs with hex
  · obtain ⟨A, B, hAB, gAB⟩ := hex
    have hAB' : A ^ 2 + 27 * B ^ 2 = (q : ℤ) ^ j := by rw [hAB]; push_cast; rfl
    have hA0 : A ≠ 0 := fun h => not_dvd_fst hq hj h27 hAB' gAB (h ▸ dvd_zero _)
    have hB0 : B ≠ 0 := fun h => not_dvd_snd hq hj h27 hAB' gAB (h ▸ dvd_zero _)
    have hA' : 0 < |A| := abs_pos.2 hA0
    have hB' : 0 < |B| := abs_pos.2 hB0
    have hS : (Icc (-((q ^ j : ℕ) : ℤ)) ((q ^ j : ℕ) : ℤ) ×ˢ Icc (-((q ^ j : ℕ) : ℤ)) ((q ^ j : ℕ) : ℤ)).filter
        (fun ab : ℤ × ℤ => ab.1 ^ 2 + 27 * ab.2 ^ 2 = ((q ^ j : ℕ) : ℤ) ∧ Int.gcd ab.1 ab.2 = 1)
        = {(|A|, |B|), (-|A|, |B|), (|A|, -|B|), (-|A|, -|B|)} := by
      ext ⟨c, d⟩
      rw [mem_rStarSet]
      simp only [mem_insert, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨h1, g1⟩
        have h1' : c ^ 2 + 27 * d ^ 2 = (q : ℤ) ^ j := by rw [h1]; push_cast; rfl
        obtain ⟨e1, e2⟩ := prim_rep_unique hq hq2 (by norm_num) h27 hj hAB' gAB h1' g1
        rw [← sq_abs A, eq_comm, sq_eq_sq_iff_eq_or_eq_neg] at e1
        rw [← sq_abs B, eq_comm, sq_eq_sq_iff_eq_or_eq_neg] at e2
        rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> simp [e1, e2]
      · intro h
        apply rep_of_sq_eq hAB gAB
        · rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [sq_abs]
        · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [sq_abs]
    rw [hS, card_insert_of_notMem (by simp [Prod.ext_iff]; omega),
      card_insert_of_notMem (by simp [Prod.ext_iff]; omega),
      card_insert_of_notMem (by simp [Prod.ext_iff]; omega), card_singleton]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨c, d⟩ - ⟨h1, g1⟩
    exact hex ⟨c, d, h1, g1⟩

open Classical in
/-- **(b)**: for a prime `q > 3` and `j ≥ 1`, `Wfun (q^j) ∈ {0, 4}`. -/
theorem Wfun_prime_pow_zero_or_four {q j : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hj : 1 ≤ j) :
    Wfun (q ^ j) = 0 ∨ Wfun (q ^ j) = 4 := by
  rw [Wfun_prime_pow_eq_rStar hq hq3 hj, rStar_prime_pow hq hq3 hj]
  split_ifs <;> simp

/-! ## Part (a): `q ≡ 2 (mod 3)` -/

lemma zmod_intCast_ne_zero {q : ℕ} {m : ℤ} (h : ¬ (q : ℤ) ∣ m) : ((m : ℤ) : ZMod q) ≠ 0 :=
  fun e => h ((ZMod.intCast_zmod_eq_zero_iff_dvd m q).1 e)

lemma not_dvd_small {q : ℕ} (hq3 : 3 < q) {m : ℤ} (h0 : 0 < m) (hm : m ≤ 3) :
    ¬ (q : ℤ) ∣ m := by
  intro h
  have := Int.le_of_dvd h0 h
  omega

/-- If `-3` is a square mod a prime `q > 3`, then `q ≡ 1 (mod 3)`. -/
lemma mod_three_of_sq_eq_neg_three {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) {s : ZMod q}
    (hs : s ^ 2 = -3) : q % 3 = 1 := by
  have := Fact.mk hq
  have h2 : (2 : ZMod q) ≠ 0 := by
    have := zmod_intCast_ne_zero (not_dvd_small hq3 (m := 2) (by norm_num) (by norm_num))
    simpa using this
  have h3 : (3 : ZMod q) ≠ 0 := by
    have := zmod_intCast_ne_zero (not_dvd_small hq3 (m := 3) (by norm_num) (by norm_num))
    simpa using this
  set w : ZMod q := (s - 1) * 2⁻¹ with hw
  have h2w : 2 * w = s - 1 := by rw [hw, mul_comm, mul_assoc, inv_mul_cancel₀ h2, mul_one]
  have h4 : 4 * (w ^ 2 + w + 1) = 0 := by linear_combination (2 * w + s + 1) * h2w + hs
  have hw0 : w ^ 2 + w + 1 = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (by linear_combination h : (2 : ZMod q) * 2 = 0) (mul_ne_zero h2 h2)
    · exact h
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw0
  have hw1 : w ≠ 1 := by
    intro h; apply h3; rw [h] at hw0; linear_combination hw0
  have hord : orderOf w = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hw3 hw1
  have hwne : w ≠ 0 := by intro h; rw [h] at hw3; norm_num at hw3
  have := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hwne)
  rw [hord] at this
  have := hq.two_le
  omega

/-- A primitive representation of `q^j` by `x^2 + 27 y^2` forces `q ≡ 1 (mod 3)`. -/
lemma mod_three_of_rep {q j : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hj : 1 ≤ j) {a b : ℤ}
    (h : a ^ 2 + 27 * b ^ 2 = (q : ℤ) ^ j) (g : Int.gcd a b = 1) : q % 3 = 1 := by
  have := Fact.mk hq
  have hb := zmod_intCast_ne_zero (not_dvd_snd hq hj (not_dvd_27 hq hq3) h g)
  have h3 : (3 : ZMod q) ≠ 0 := by
    have := zmod_intCast_ne_zero (not_dvd_small hq3 (m := 3) (by norm_num) (by norm_num))
    simpa using this
  have hz : (a : ZMod q) ^ 2 + 27 * (b : ZMod q) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) h
    push_cast at this
    rw [this, ZMod.natCast_self, zero_pow (by omega)]
  apply mod_three_of_sq_eq_neg_three hq hq3 (s := (a : ZMod q) * (3 * (b : ZMod q))⁻¹)
  have hu : (3 * (b : ZMod q)) * (3 * (b : ZMod q))⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h3 hb)
  linear_combination ((3 * (b : ZMod q))⁻¹) ^ 2 * hz
    - 3 * (3 * (b : ZMod q) * (3 * (b : ZMod q))⁻¹ + 1) * hu

/-- **(a)**: `Wfun (q^j) = 0` for every prime `q ≡ 2 (mod 3)` and `j ≥ 1`. -/
theorem Wfun_prime_pow_of_mod_three_eq_two {q j : ℕ} (hq : q.Prime) (h2 : q % 3 = 2)
    (hj : 1 ≤ j) : Wfun (q ^ j) = 0 := by
  rcases Nat.lt_or_ge 3 q with hq3 | hq3
  · rw [Wfun_prime_pow_eq_rStar hq hq3 hj, rStar_prime_pow hq hq3 hj]
    split_ifs with hex
    · exfalso
      obtain ⟨a, b, h, g⟩ := hex
      have h' : a ^ 2 + 27 * b ^ 2 = (q : ℤ) ^ j := by rw [h]; push_cast; rfl
      have := mod_three_of_rep hq hq3 hj h' g
      omega
    · rfl
  · have hq2 : q = 2 := by
      have := hq.two_le; interval_cases q <;> simp_all
    subst hq2
    rw [Wfun, ite_eq_right]
    intro hc
    have := Nat.Coprime.coprime_dvd_left (dvd_pow_self 2 (by omega)) hc
    norm_num at this

/-! ## Part (c): Fermat for `x^2 + 3 y^2`, powers in `ℤ√-3`, and the exact value -/

/-- `-3` is a square mod a prime `q ≡ 1 (mod 3)` (a cube root of unity `w` gives `(2w+1)^2 = -3`). -/
lemma exists_sq_eq_neg_three {q : ℕ} (hq : q.Prime) (h1 : q % 3 = 1) :
    ∃ s : ZMod q, s ^ 2 = -3 := by
  have := Fact.mk hq
  have h3 : 3 ∣ Fintype.card (ZMod q)ˣ := by rw [ZMod.card_units]; omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hw3 : (g : ZMod q) ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hw1 : (g : ZMod q) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext h
    rw [this, orderOf_one] at hg; norm_num at hg
  have hw0 : (g : ZMod q) ^ 2 + g + 1 = 0 := by
    have : ((g : ZMod q) - 1) * ((g : ZMod q) ^ 2 + g + 1) = 0 := by linear_combination hw3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hw1)
  exact ⟨2 * g + 1, by linear_combination 4 * hw0⟩

/-- **Fermat for `x^2 + 3y^2`**: a prime `q ≡ 1 (mod 3)` is `x^2 + 3 y^2` (Thue's lemma). -/
theorem fermat_three {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (h1 : q % 3 = 1) :
    ∃ x y : ℤ, x ^ 2 + 3 * y ^ 2 = q := by
  have := Fact.mk hq
  obtain ⟨s, hs⟩ := exists_sq_eq_neg_three hq h1
  set m := Nat.sqrt q with hm
  have hmq : m * m < q := by
    have hle : m * m ≤ q := Nat.sqrt_le q
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hd : m ∣ q := ⟨m, h.symm⟩
      rcases hq.eq_one_or_self_of_dvd m hd with h' | h'
      · rw [h'] at h; omega
      · rw [h'] at h; nlinarith [hq.two_le]
  have hcard : (univ : Finset (ZMod q)).card < (range (m + 1) ×ˢ range (m + 1)).card := by
    rw [card_univ, ZMod.card, card_product, card_range]
    have := Nat.lt_succ_sqrt' q
    rw [← hm] at this
    simpa [sq] using this
  obtain ⟨⟨u1, v1⟩, hu, ⟨u2, v2⟩, hv, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun uv : ℕ × ℕ => ((uv.1 : ZMod q) - s * (uv.2 : ZMod q)))
    (fun _ _ => mem_coe.2 (mem_univ _))
  simp only [mem_product, mem_range] at hu hv
  simp only at heq
  have hxy0 : (u1 : ℤ) - u2 ≠ 0 ∨ (v1 : ℤ) - v2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    simp only [Prod.mk.injEq]
    omega
  set x : ℤ := (u1 : ℤ) - u2 with hx
  set y : ℤ := (v1 : ℤ) - v2 with hy
  have hdiv : (q : ℤ) ∣ x ^ 2 + 3 * y ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have e : (x : ZMod q) = s * (y : ZMod q) := by
      rw [hx, hy]; push_cast; linear_combination heq
    push_cast; rw [e]; linear_combination (y : ZMod q) ^ 2 * hs
  have hmz : ((m : ℤ) * m) < q := by exact_mod_cast hmq
  have hxb : x ^ 2 ≤ (m : ℤ) * m := by
    have a1 : x ≤ m := by omega
    have a2 : -(m : ℤ) ≤ x := by omega
    nlinarith
  have hyb : y ^ 2 ≤ (m : ℤ) * m := by
    have a1 : y ≤ m := by omega
    have a2 : -(m : ℤ) ≤ y := by omega
    nlinarith
  have hpos : 0 < x ^ 2 + 3 * y ^ 2 := by
    rcases hxy0 with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg y]
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg x]
  obtain ⟨k, hk⟩ := hdiv
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hk0 : 0 < k := by
    by_contra h; push Not at h; nlinarith
  have hk4 : k < 4 := by
    by_contra h; push Not at h; nlinarith
  interval_cases k
  · exact ⟨x, y, by linarith⟩
  · exfalso
    obtain ⟨r, hr⟩ := hq.eq_two_or_odd'.resolve_left (by omega)
    have e : x ^ 2 + 3 * y ^ 2 = 4 * r + 2 := by rw [hk, hr]; push_cast; ring
    have e4 := congrArg (fun z : ℤ => (z : ZMod 4)) e
    push_cast at e4
    rw [show (4 : ZMod 4) = 0 by decide, zero_mul, zero_add] at e4
    generalize (x : ZMod 4) = X at e4
    generalize (y : ZMod 4) = Y at e4
    revert X Y; decide
  · have h3x : (3 : ℤ) ∣ x := Int.prime_three.dvd_of_dvd_pow (n := 2)
      ⟨q - y ^ 2, by linear_combination hk⟩
    obtain ⟨x', hx'⟩ := h3x
    refine ⟨y, x', ?_⟩
    have : (3 : ℤ) * (y ^ 2 + 3 * x' ^ 2) = 3 * q := by linear_combination hk - (x + 3 * x') * hx'
    exact mul_left_cancel₀ (by norm_num) this

lemma norm_pow' (z : ℤ√(-3)) (j : ℕ) : (z ^ j).norm = z.norm ^ j := by
  induction j with
  | zero => simp
  | succ n ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

lemma norm_pow_eq {x y : ℤ} {q : ℕ} (h : x ^ 2 + 3 * y ^ 2 = q) (j : ℕ) :
    ((⟨x, y⟩ : ℤ√(-3)) ^ j).re ^ 2 + 3 * ((⟨x, y⟩ : ℤ√(-3)) ^ j).im ^ 2 = (q : ℤ) ^ j := by
  have hn : ∀ z : ℤ√(-3), z.norm = z.re ^ 2 + 3 * z.im ^ 2 := fun z => by
    rw [Zsqrtd.norm_def]; ring
  rw [← hn, norm_pow', hn]
  simp [h]

/-- Powers of a norm `q` element of `ℤ√-3` are primitive (`q > 3` prime). -/
theorem gcd_pow_eq_one {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) {x y : ℤ}
    (hxy : x ^ 2 + 3 * y ^ 2 = q) (j : ℕ) :
    Int.gcd ((⟨x, y⟩ : ℤ√(-3)) ^ j).re ((⟨x, y⟩ : ℤ√(-3)) ^ j).im = 1 := by
  set α : ℤ√(-3) := ⟨x, y⟩ with hα
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hN := norm_pow_eq hxy j
  by_contra hg
  obtain ⟨p, hp', hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpu : (p : ℤ) ∣ (α ^ j).re := (Int.natCast_dvd_natCast.2 hpg).trans (Int.gcd_dvd_left _ _)
  have hpv : (p : ℤ) ∣ (α ^ j).im := (Int.natCast_dvd_natCast.2 hpg).trans (Int.gcd_dvd_right _ _)
  have hpq : (p : ℤ) ∣ (q : ℤ) ^ j := by
    rw [← hN]
    exact dvd_add (dvd_pow hpu two_ne_zero) (dvd_mul_of_dvd_right (dvd_pow hpv two_ne_zero) _)
  have hpq' : p = q := by
    have : p ∣ q ^ j := by exact_mod_cast hpq
    exact (Nat.prime_dvd_prime_iff_eq hp' hq).1 (hp'.dvd_of_dvd_pow this)
  rw [hpq'] at hpu hpv
  set I : Ideal (ℤ√(-3)) := Ideal.span {((q : ℤ) : ℤ√(-3))}
  have h1 : α ^ j ∈ I := Ideal.mem_span_singleton.2 ((Zsqrtd.intCast_dvd _ _).2 ⟨hpu, hpv⟩)
  have h2 : (star α) ^ j ∈ I := by
    rw [← star_pow]
    exact Ideal.mem_span_singleton.2 ((Zsqrtd.intCast_dvd _ _).2
      ⟨by simpa [-star_pow] using hpu, by simpa [-star_pow] using hpv⟩)
  have h3 := Ideal.add_pow_mem_of_pow_mem_of_le I h1 h2 (k := 2 * j) (by omega)
  have hsum : α + star α = ((2 * x : ℤ) : ℤ√(-3)) := by
    ext <;> simp [hα]; ring
  rw [hsum, ← Int.cast_pow, Ideal.mem_span_singleton, Zsqrtd.intCast_dvd_intCast] at h3
  have h2x : (q : ℤ) ∣ 2 * x := hp.dvd_of_dvd_pow h3
  rcases hp.dvd_or_dvd h2x with h | h
  · exact absurd (Int.le_of_dvd two_pos h) (by omega)
  · have h3y : (q : ℤ) ∣ 3 * y ^ 2 := by
      have : (q : ℤ) ∣ x ^ 2 + 3 * y ^ 2 := hxy ▸ dvd_refl _
      exact (dvd_add_right (dvd_pow h two_ne_zero)).1 this
    rcases hp.dvd_or_dvd h3y with h' | h'
    · exact not_dvd_small hq3 (by norm_num) (by norm_num) h'
    · have hy := hp.dvd_of_dvd_pow h'
      obtain ⟨a, ha⟩ := h
      obtain ⟨b, hb⟩ := hy
      have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
      have : (q : ℤ) * (q * (a ^ 2 + 3 * b ^ 2)) = q * 1 := by
        linear_combination hxy - (x + q * a) * ha - 3 * (y + q * b) * hb
      have e := mul_left_cancel₀ hq0.ne' this
      have := Int.le_of_dvd one_pos ⟨_, e.symm⟩
      omega

lemma three_dvd_iff_zmod (a : ℤ) : (3 : ℤ) ∣ a ↔ (a : ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

/-- `ℤ√-3` powers mod 3: `(x + y√-3)^(n+1) ≡ x^(n+1) + (n+1) x^n y √-3`. -/
lemma pow_mod_three (x y : ℤ) (n : ℕ) :
    (3 : ℤ) ∣ ((⟨x, y⟩ : ℤ√(-3)) ^ (n + 1)).re - x ^ (n + 1) ∧
    (3 : ℤ) ∣ ((⟨x, y⟩ : ℤ√(-3)) ^ (n + 1)).im - ((n : ℤ) + 1) * x ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    constructor
    · exact ⟨a * x - ((⟨x, y⟩ : ℤ√(-3)) ^ (n + 1)).im * y, by linear_combination x * ha⟩
    · exact ⟨a * y + b * x, by linear_combination y * ha + x * hb⟩

/-- The set `R`: primes of the form `a^2 + 27 b^2`. -/
def R27 (q : ℕ) : Prop := q.Prime ∧ ∃ a b : ℤ, a ^ 2 + 27 * b ^ 2 = q

theorem R27_spec (q : ℕ) (h : R27 q) : q.Prime ∧ 3 < q ∧ q % 3 = 1 := by
  obtain ⟨hq, a, b, hab⟩ := h
  have h3a : (a : ZMod 3) ≠ 0 := by
    rw [Ne, ← three_dvd_iff_zmod]
    rintro ⟨c, rfl⟩
    have : (3 : ℤ) ∣ q := ⟨3 * c ^ 2 + 9 * b ^ 2, by rw [← hab]; ring⟩
    have h3 : (3 : ℕ) ∣ q := by exact_mod_cast this
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h3
    subst this
    have e : 9 * c ^ 2 + 27 * b ^ 2 = 3 := by push_cast at hab; linear_combination hab
    generalize c ^ 2 = C at e
    generalize b ^ 2 = B at e
    omega
  have hz : ((q : ℕ) : ZMod 3) = (a : ZMod 3) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) hab
    push_cast at this
    rw [← this, show (27 : ZMod 3) = 0 by decide]; ring
  have hsq : ∀ t : ZMod 3, t ≠ 0 → t ^ 2 = 1 := by decide
  have h1 : q % 3 = 1 := by
    have := congrArg ZMod.val hz
    rw [ZMod.val_natCast, hsq _ h3a] at this
    exact this
  have := hq.two_le
  exact ⟨hq, by omega, h1⟩

/-- **Exact criterion**: for a prime `q > 3`, `q ≡ 1 (mod 3)`, and `j ≥ 1`, `q^j` has a primitive
representation by `x^2 + 27 y^2` iff `q ∈ R` or `3 ∣ j`. -/
theorem exists_rep_iff {q j : ℕ} (hq : q.Prime) (hq3 : 3 < q) (h1 : q % 3 = 1) (hj : 1 ≤ j) :
    (∃ a b : ℤ, a ^ 2 + 27 * b ^ 2 = ((q ^ j : ℕ) : ℤ) ∧ Int.gcd a b = 1) ↔ (R27 q ∨ 3 ∣ j) := by
  obtain ⟨x, y, hxy⟩ := fermat_three hq hq3 h1
  have hq2 : q ≠ 2 := by omega
  have h3q : ¬ (q : ℤ) ∣ 3 := not_dvd_small hq3 (by norm_num) (by norm_num)
  have huv : ((⟨x, y⟩ : ℤ√(-3)) ^ j).re ^ 2 + 3 * ((⟨x, y⟩ : ℤ√(-3)) ^ j).im ^ 2 = (q : ℤ) ^ j :=
    norm_pow_eq hxy j
  have guv := gcd_pow_eq_one hq hq3 hxy j
  set u := ((⟨x, y⟩ : ℤ√(-3)) ^ j).re with hu
  set v := ((⟨x, y⟩ : ℤ√(-3)) ^ j).im with hv
  have three_ndvd_q : ¬ (3 : ℤ) ∣ (q : ℤ) ^ j := by
    intro h
    have h' : (3 : ℕ) ∣ q ^ j := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.prime_three.dvd_of_dvd_pow h')
    omega
  have step1 : (∃ a b : ℤ, a ^ 2 + 27 * b ^ 2 = ((q ^ j : ℕ) : ℤ) ∧ Int.gcd a b = 1)
      ↔ (3 : ℤ) ∣ v := by
    constructor
    · rintro ⟨a, b, hab, gab⟩
      push_cast at hab
      have h3a : ¬ (3 : ℤ) ∣ a := by
        intro h; apply three_ndvd_q; rw [← hab]
        exact dvd_add (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_left ⟨9, by norm_num⟩ _)
      have g' : Int.gcd a (3 * b) = 1 := by
        rw [← Int.isCoprime_iff_gcd_eq_one] at gab ⊢
        exact IsCoprime.mul_right ((Int.prime_three.coprime_iff_not_dvd.2 h3a).symm) gab
      have e : a ^ 2 + 3 * (3 * b) ^ 2 = (q : ℤ) ^ j := by rw [← hab]; ring
      obtain ⟨-, e2⟩ := prim_rep_unique hq hq2 (by norm_num) h3q hj e g' huv guv
      exact Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨3 * b ^ 2, by rw [← e2]; ring⟩
    · rintro ⟨w, hw⟩
      refine ⟨u, w, by push_cast; rw [← huv, hw]; ring, ?_⟩
      have := Int.isCoprime_iff_gcd_eq_one.2 guv
      rw [hw] at this
      exact Int.isCoprime_iff_gcd_eq_one.1 this.of_mul_right_right
  have gxy : Int.gcd x y = 1 := by simpa using gcd_pow_eq_one hq hq3 hxy 1
  have step3 : R27 q ↔ (3 : ℤ) ∣ y := by
    constructor
    · rintro ⟨-, a, b, hab⟩
      have e : a ^ 2 + 3 * (3 * b) ^ 2 = q := by rw [← hab]; ring
      have g' : Int.gcd a (3 * b) = 1 := by simpa using gcd_pow_eq_one hq hq3 e 1
      have e' : a ^ 2 + 3 * (3 * b) ^ 2 = (q : ℤ) ^ 1 := by rw [pow_one, e]
      have hxy' : x ^ 2 + 3 * y ^ 2 = (q : ℤ) ^ 1 := by rw [pow_one, hxy]
      obtain ⟨-, e2⟩ := prim_rep_unique hq hq2 (by norm_num) h3q le_rfl e' g' hxy' gxy
      exact Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨3 * b ^ 2, by rw [← e2]; ring⟩
    · rintro ⟨y', rfl⟩
      exact ⟨hq, x, y', by rw [← hxy]; ring⟩
  have hx3 : ¬ (3 : ℤ) ∣ x := by
    intro h; apply three_ndvd_q
    exact dvd_pow (by rw [← hxy]; exact dvd_add (dvd_pow h two_ne_zero) (dvd_mul_right _ _))
      (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have step2 : (3 : ℤ) ∣ v ↔ (3 ∣ n + 1 ∨ (3 : ℤ) ∣ y) := by
    obtain ⟨b, hb⟩ := (pow_mod_three x y n).2
    rw [← hv] at hb
    have e : v = ((n : ℤ) + 1) * x ^ n * y + 3 * b := by linear_combination hb
    rw [e, dvd_add_left (dvd_mul_right (3 : ℤ) b), Int.prime_three.dvd_mul,
      Int.prime_three.dvd_mul]
    have hxn : ¬ (3 : ℤ) ∣ x ^ n := fun h => hx3 (Int.prime_three.dvd_of_dvd_pow h)
    have hn : (3 : ℤ) ∣ (n : ℤ) + 1 ↔ 3 ∣ n + 1 := by
      constructor <;> intro h <;> exact_mod_cast h
    rw [hn]
    tauto
  rw [step1, step2, step3, or_comm]

noncomputable instance : DecidablePred R27 := Classical.decPred _

lemma ite_of_not {p : Prop} [Decidable p] (h : ¬ p) (a b : ℤ) : (if p then a else b) = b := by
  simp [h]

/-- **(N2)** for `W = Wfun` and `R = R27`, exactly in the form of the hypothesis `hWpp`. -/
theorem Wfun_prime_pow (q j : ℕ) (hq : q.Prime) (hj : 1 ≤ j) :
    Wfun (q ^ j) = if 3 < q ∧ q % 3 = 1 ∧ (R27 q ∨ 3 ∣ j) then 4 else 0 := by
  rcases Nat.lt_or_ge 3 q with hq3 | hq3
  · have hq0 : q % 3 ≠ 0 := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h1 | h2
    · rw [Wfun_prime_pow_eq_rStar hq hq3 hj, rStar_prime_pow hq hq3 hj]
      simp only [exists_rep_iff hq hq3 h1 hj, hq3, h1, true_and]
      split_ifs <;> rfl
    · rw [Wfun_prime_pow_of_mod_three_eq_two hq h2 hj, ite_of_not (fun h => by omega)]
  · rw [ite_of_not (fun h => absurd h.1 (by omega)), Wfun, ite_eq_right]
    intro hc
    have hq6 : q ∣ 6 := by
      have := hq.two_le
      interval_cases q <;> norm_num
    have := Nat.Coprime.coprime_dvd_left (dvd_pow_self q (by omega)) hc
    rw [Nat.Prime.coprime_iff_not_dvd hq] at this
    exact this hq6

/-! ## Theorem L, unconditional -/

/-- **Theorem L, summed exact form**, unconditional for `W = Wfun`, `R = R27`. -/
theorem L_summed_exact_Wfun {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, Wfun n
      = 1 + 4 * ((piR R27 x : ℤ) + CR R27 x)
        + ∑ n ∈ (Ioc 0 x).filter (fun n => 2 ≤ ω n), Wfun n :=
  L_summed_exact Wfun R27_spec Wfun_one Wfun_prime_pow hx

/-- **Theorem L, mod 8**, unconditional. -/
theorem L_summed_mod8_Wfun {x : ℕ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 x, Wfun n ≡ 1 + 4 * ((piR R27 x : ℤ) + CR R27 x) [ZMOD 8] :=
  L_summed_mod8 Wfun R27_spec Wfun_one (fun _ h => Wfun_eight_dvd h) Wfun_prime_pow hx

/-- **(N3)**, unconditional. -/
theorem L_N3_Wfun {x : ℕ} (hx : 1 ≤ x) :
    (4 : ℤ) ∣ ∑ n ∈ Ioc 0 x, Wfun n - 1 ∧
      (piR R27 x : ℤ) ≡ (∑ n ∈ Ioc 0 x, Wfun n - 1) / 4 - CR R27 x [ZMOD 2] :=
  L_N3 Wfun R27_spec Wfun_one (fun _ h => Wfun_eight_dvd h) Wfun_prime_pow hx

end M2L6n

#print axioms M2L6n.Wfun_prime_pow_of_mod_three_eq_two
#print axioms M2L6n.Wfun_prime_pow_zero_or_four
#print axioms M2L6n.Wfun_prime_pow
#print axioms M2L6n.L_summed_exact_Wfun
#print axioms M2L6n.L_summed_mod8_Wfun
#print axioms M2L6n.L_N3_Wfun
