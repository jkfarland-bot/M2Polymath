/-
  Seat M2L5, item 4: Result N (A19 section 9b) as a positive tuple count.
  c_L(n) is the number of positive tuples (u_0, v_0, ..., u_{L-1}, v_{L-1}) with
  n = ∏_r (u_r v_r)^(3^r); and (N5): for every x and every depth L with ⌊x^(1/3)⌋ < 2^(3^L),
  π(x) ≡ ∑_{1 ≤ j ≤ ⌊log₂ x⌋} w_j T_{j,L}(x) (mod 3), w_j = j μ(j) mod 3, where T_{j,L}(x) counts the
  positive tuples (a, b, c, u_0, v_0, ...) with a ≤ b, a < c, (abc)^j ∏_r (u_r v_r)^(j 3^(r+1)) ≤ x.
-/
import Mathlib
import M2ResultN

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace M2L5

open M2L3 M2L4

/-! ## Tuples -/

/-- The box `[1, N]²` for one pair `(u_r, v_r)`. -/
def BB (N : ℕ) : Finset (ℕ × ℕ) := Icc 1 N ×ˢ Icc 1 N

/-- `P(t) = ∏_{r < L} (u_r v_r)^(3^r)`. -/
def Ptup (L : ℕ) (t : Fin L → ℕ × ℕ) : ℕ := ∏ r : Fin L, ((t r).1 * (t r).2) ^ (3 ^ (r : ℕ))

/-- The tuples in the box `[1, N]^(2L)` with `P(t) = n`. -/
def tupSet (L N n : ℕ) : Finset (Fin L → ℕ × ℕ) :=
  (Fintype.piFinset fun _ => BB N).filter (fun t => Ptup L t = n)

lemma Ptup_cons {L : ℕ} (p : ℕ × ℕ) (t : Fin L → ℕ × ℕ) :
    Ptup (L + 1) (Fin.cons p t : Fin (L + 1) → ℕ × ℕ) = p.1 * p.2 * Ptup L t ^ 3 := by
  unfold Ptup
  rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.val_zero, pow_zero, pow_one, ← prod_pow]
  congr 1
  refine prod_congr rfl fun r _ => ?_
  rw [Fin.cons_succ, Fin.val_succ, ← pow_mul, pow_succ]

lemma sum_piFinset_cons {β M : Type*} [AddCommMonoid M] {L : ℕ} (S : Finset β)
    (g : (Fin (L + 1) → β) → M) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (L + 1) => S), g t
      = ∑ p ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin L => S), g (Fin.cons p t) := by
  have h := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (L + 1) => S)
    (fun _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), filter_true_of_mem (fun _ _ => trivial)] at h
  rw [h, sum_map, sum_product]
  rfl

lemma Ptup_pos {L N : ℕ} {t : Fin L → ℕ × ℕ} (ht : t ∈ Fintype.piFinset fun _ => BB N) :
    1 ≤ Ptup L t := by
  unfold Ptup
  apply Nat.one_le_iff_ne_zero.2
  rw [prod_ne_zero_iff]
  intro r _
  have := Fintype.mem_piFinset.1 ht r
  simp only [BB, mem_product, mem_Icc] at this
  exact pow_ne_zero _ (Nat.mul_ne_zero (by omega) (by omega))

lemma d2Z_box {a N : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) :
    d2Z a = ∑ p ∈ BB N, if p.1 * p.2 = a then (1 : ℤ) else 0 := by
  rw [d2Z, mul_apply, ← natCast_card_filter]
  have e : ∀ x ∈ a.divisorsAntidiagonal, (ζ : ArithmeticFunction ℤ) x.1 * (ζ : ArithmeticFunction ℤ) x.2 = 1 := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have h1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hx; omega
    have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hx; omega
    simp [natCoe_apply, zeta_apply, h1, h2]
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul, mul_one]
  congr 1
  congr 1
  ext x
  simp only [Nat.mem_divisorsAntidiagonal, BB, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨hx, -⟩
    have h1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hx; omega
    have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hx; omega
    have := Nat.le_mul_of_pos_right x.1 (Nat.pos_of_ne_zero h2)
    have := Nat.le_mul_of_pos_left x.2 (Nat.pos_of_ne_zero h1)
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hx⟩
  · rintro ⟨-, hx⟩; exact ⟨hx, by omega⟩

lemma Ek3_box (f : ArithmeticFunction ℤ) {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) :
    Ek 3 f b = ∑ m ∈ Icc 1 N, if m ^ 3 = b then f m else 0 := by
  by_cases h : ∃ m, m ^ 3 = b
  · obtain ⟨m, rfl⟩ := h
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h; · simp at hb
      exact h
    have hmN : m ≤ N := (Nat.le_self_pow (by norm_num) m).trans hbN
    rw [Ek_pow (by norm_num), sum_eq_single_of_mem m (mem_Icc.2 ⟨hm1, hmN⟩), if_pos rfl]
    intro c _ hc
    rw [if_neg (fun h => hc (Nat.pow_left_injective (by norm_num) h))]
  · rw [Ek_notpow _ (fun c hc => h ⟨c, hc⟩)]
    exact (sum_eq_zero fun c _ => if_neg (fun hc => h ⟨c, hc⟩)).symm

lemma cL_succ_box (L : ℕ) {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (cL (L + 1) n : ℤ) = ∑ p ∈ BB N, ∑ m ∈ Icc 1 N, if p.1 * p.2 * m ^ 3 = n then cL L m else 0 := by
  rw [cL, mul_apply]
  have e : ∀ x ∈ n.divisorsAntidiagonal, d2Z x.1 * Ek 3 (cL L) x.2
      = ∑ p ∈ BB N, ∑ m ∈ Icc 1 N, if (p.1 * p.2, m ^ 3) = x then cL L m else 0 := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have h1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hx; omega
    have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hx; omega
    have := Nat.le_mul_of_pos_right x.1 (Nat.pos_of_ne_zero h2)
    have := Nat.le_mul_of_pos_left x.2 (Nat.pos_of_ne_zero h1)
    rw [d2Z_box (N := N) (by omega) (by omega), Ek3_box _ (N := N) (by omega) (by omega), sum_mul]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    by_cases ha : p.1 * p.2 = x.1 <;> by_cases hb : m ^ 3 = x.2 <;> simp [ha, hb, Prod.ext_iff]
  rw [sum_congr rfl e, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_ite_eq]
  simp only [Nat.mem_divisorsAntidiagonal]
  by_cases h : p.1 * p.2 * m ^ 3 = n
  · rw [if_pos ⟨h, by omega⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/-- **`c_L` as a positive tuple count**: for `1 ≤ n ≤ N`, `c_L(n)` is the number of tuples
`(u_0, v_0, ..., u_{L-1}, v_{L-1})` in `[1, N]^(2L)` with `n = ∏_r (u_r v_r)^(3^r)`. (Every such tuple has
all entries `≤ n`, so the count does not depend on `N ≥ n`.) -/
theorem cL_count (L : ℕ) : ∀ N n : ℕ, 1 ≤ n → n ≤ N → (cL L n : ℤ) = (tupSet L N n).card := by
  induction L with
  | zero =>
    intro N n hn _
    rw [cL, tupSet]
    have : (Fintype.piFinset fun _ : Fin 0 => BB N) = {Fin.elim0} := by
      ext t
      simp only [Fintype.mem_piFinset, mem_singleton]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _ i; exact i.elim0
    rw [this, filter_singleton]
    simp only [Ptup, univ_eq_empty, prod_empty, ArithmeticFunction.one_apply]
    by_cases h : n = 1
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  | succ L ih =>
    intro N n hn hnN
    rw [cL_succ_box L hn hnN, tupSet, natCast_card_filter, sum_piFinset_cons]
    refine sum_congr rfl fun p hp => ?_
    have hp' : 1 ≤ p.1 ∧ 1 ≤ p.2 := by
      simp only [BB, mem_product, mem_Icc] at hp; exact ⟨hp.1.1, hp.2.1⟩
    have e : ∀ t ∈ Fintype.piFinset (fun _ : Fin L => BB N),
        (if Ptup (L + 1) (Fin.cons p t) = n then (1 : ℤ) else 0)
          = ∑ m ∈ Icc 1 N, (if p.1 * p.2 * m ^ 3 = n then (1 : ℤ) else 0)
              * (if Ptup L t = m then 1 else 0) := by
      intro t ht
      simp only [mul_ite, mul_one, mul_zero]
      rw [sum_ite_eq, Ptup_cons]
      have h1 := Ptup_pos ht
      by_cases hm : Ptup L t ∈ Icc 1 N
      · rw [if_pos hm]
      · rw [if_neg hm, if_neg]
        have : N < Ptup L t := by simp only [mem_Icc, not_and, not_le] at hm; exact hm h1
        intro h
        have : Ptup L t ≤ p.1 * p.2 * Ptup L t ^ 3 := by
          calc Ptup L t = 1 * 1 * Ptup L t ^ 1 := by ring
            _ ≤ p.1 * p.2 * Ptup L t ^ 3 :=
              Nat.mul_le_mul (Nat.mul_le_mul hp'.1 hp'.2) (Nat.pow_le_pow_right h1 (by norm_num))
        omega
    rw [sum_congr rfl e, sum_comm]
    refine sum_congr rfl fun m hm => ?_
    rw [mem_Icc] at hm
    have := ih N m hm.1 hm.2
    rw [tupSet] at this
    rw [← mul_sum, ← natCast_card_filter, ← this]
    split_ifs <;> simp

/-! ## (N5) -/

/-- `T_{j,L}(x)`: the number of positive tuples `(a, b, c, u_0, v_0, ..., u_{L-1}, v_{L-1})` with
`a ≤ b`, `a < c` and `(abc)^j ∏_{r < L} (u_r v_r)^(j 3^(r+1)) ≤ x` (all entries are then `≤ x`). -/
def TT (j L x : ℕ) : ℕ :=
  (((Icc 1 x ×ˢ Icc 1 x ×ˢ Icc 1 x) ×ˢ Fintype.piFinset (fun _ : Fin L => BB x)).filter
    (fun s => s.1.1 ≤ s.1.2.1 ∧ s.1.1 < s.1.2.2 ∧
      (s.1.1 * s.1.2.1 * s.1.2.2) ^ j * ∏ r : Fin L, ((s.2 r).1 * (s.2 r).2) ^ (j * 3 ^ ((r : ℕ) + 1))
        ≤ x)).card

lemma prod_shift (j L : ℕ) (t : Fin L → ℕ × ℕ) :
    ∏ r : Fin L, ((t r).1 * (t r).2) ^ (j * 3 ^ ((r : ℕ) + 1)) = (Ptup L t ^ 3) ^ j := by
  rw [Ptup, ← pow_mul, ← prod_pow]
  refine prod_congr rfl fun r _ => ?_
  rw [← pow_mul]; congr 1; ring

/-- The inner count: for a fixed tuple `t`, the triples are those of `H(⌊⌊x^(1/j)⌋ / P(t)^3⌋)`. -/
lemma inner_count {j L x : ℕ} (hj : 1 ≤ j) {t : Fin L → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset fun _ => BB x) :
    ((Icc 1 x ×ˢ Icc 1 x ×ˢ Icc 1 x).filter (fun abc => abc.1 ≤ abc.2.1 ∧ abc.1 < abc.2.2 ∧
      (abc.1 * abc.2.1 * abc.2.2) ^ j * ∏ r : Fin L, ((t r).1 * (t r).2) ^ (j * 3 ^ ((r : ℕ) + 1)) ≤ x)).card
      = H (iroot j x / Ptup L t ^ 3) := by
  have hP := Ptup_pos ht
  have hP3 : 0 < Ptup L t ^ 3 := by positivity
  have hyx : iroot j x ≤ x := iroot_le hj x
  unfold H
  congr 1
  ext ⟨a, b, c⟩
  simp only [mem_Hset, mem_filter, mem_product, mem_Icc]
  rw [prod_shift, ← mul_pow, pow_le_iff_le_iroot hj, ← Nat.le_div_iff_mul_le hP3]
  have hdiv : iroot j x / Ptup L t ^ 3 ≤ x := (Nat.div_le_self _ _).trans hyx
  constructor
  · rintro ⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩, ⟨hc1, _⟩⟩, hab, hac, hle⟩
    exact ⟨by omega, by omega, by omega, hle, hab, hac⟩
  · rintro ⟨ha, hb, hc, hle, hab, hac⟩
    have h1 : a ≤ a * b * c := by
      calc a = a * 1 * 1 := by ring
        _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hb) hc
    have h2 : b ≤ a * b * c := by
      calc b = 1 * b * 1 := by ring
        _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul ha le_rfl) hc
    have h3 : c ≤ a * b * c := by
      calc c = 1 * 1 * c := by ring
        _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul ha hb) le_rfl
    exact ⟨⟨⟨ha, by omega⟩, ⟨hb, by omega⟩, ⟨hc, by omega⟩⟩, hab, hac, hle⟩

/-- `T_{j,L}(x) = ∑_{c ≤ x} c_L(c) H(⌊⌊x^(1/j)⌋ / c^3⌋)` for `j ≥ 1`. -/
theorem TT_eq {j L x : ℕ} (hj : 1 ≤ j) :
    (TT j L x : ℤ) = ∑ c ∈ Icc 1 x, (cL L c : ℤ) * H (iroot j x / c ^ 3) := by
  rw [TT, card_filter, sum_product_right]
  have e1 : ∀ t ∈ Fintype.piFinset (fun _ : Fin L => BB x),
      (∑ abc ∈ Icc 1 x ×ˢ Icc 1 x ×ˢ Icc 1 x,
        if abc.1 ≤ abc.2.1 ∧ abc.1 < abc.2.2 ∧
          (abc.1 * abc.2.1 * abc.2.2) ^ j * ∏ r : Fin L, ((t r).1 * (t r).2) ^ (j * 3 ^ ((r : ℕ) + 1)) ≤ x
        then 1 else 0)
        = H (iroot j x / Ptup L t ^ 3) := by
    intro t ht
    rw [← card_filter, inner_count hj ht]
  rw [Nat.cast_sum, sum_congr rfl (fun t ht => by rw [e1 t ht])]
  have e2 : ∀ t ∈ Fintype.piFinset (fun _ : Fin L => BB x),
      ((H (iroot j x / Ptup L t ^ 3) : ℕ) : ℤ)
        = ∑ c ∈ Icc 1 x, if Ptup L t = c then (H (iroot j x / c ^ 3) : ℤ) else 0 := by
    intro t ht
    rw [sum_ite_eq]
    by_cases hc : Ptup L t ∈ Icc 1 x
    · rw [if_pos hc]
    · rw [if_neg hc]
      have hP := Ptup_pos ht
      have hgt : x < Ptup L t := by simp only [mem_Icc, not_and, not_le] at hc; exact hc hP
      have : iroot j x / Ptup L t ^ 3 = 0 := by
        apply Nat.div_eq_of_lt
        calc iroot j x ≤ x := iroot_le hj x
          _ < Ptup L t := hgt
          _ ≤ Ptup L t ^ 3 := Nat.le_self_pow (by norm_num) _
      rw [this, H_zero]; simp
  rw [sum_congr rfl e2, sum_comm]
  refine sum_congr rfl fun c hc => ?_
  rw [mem_Icc] at hc
  have hcount := cL_count L x c hc.1 hc.2
  rw [tupSet] at hcount
  rw [hcount, natCast_card_filter, sum_mul]
  refine sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/-- The weights `w_j = j μ(j) mod 3 ∈ {0, 1, 2}` of (N5). -/
def wN (j : ℕ) : ℤ := ((j : ℤ) * μ j) % 3

/-- **(N5)**: for every natural `x` and every depth `L` with `⌊x^(1/3)⌋ < 2^(3^L)`,
`π(x) ≡ ∑_{1 ≤ j ≤ ⌊log₂ x⌋} w_j T_{j,L}(x) (mod 3)`, with `w_j = j μ(j) mod 3 ∈ {0, 1, 2}` and
`T_{j,L}(x)` the positive tuple count above: a single positive counting problem modulo 3. -/
theorem N5 (x L : ℕ) (hL : icbrt x < 2 ^ (3 ^ L)) :
    (Nat.primeCounting x : ℤ) ≡ ∑ j ∈ Icc 1 (Nat.log 2 x), wN j * (TT j L x : ℤ) [ZMOD 3] := by
  rw [primeCounting_M4]
  refine Int.ModEq.sum fun j hj => ?_
  have hj1 : 1 ≤ j := (mem_Icc.1 hj).1
  set y := iroot j x
  have hyx : y ≤ x := iroot_le hj1 x
  have hw : wN j ≡ (j : ℤ) * μ j [ZMOD 3] := Int.mod_modEq _ _
  -- G(y) ≡ ∑ μ(c) H(y/c³) ≡ ∑ c_L(c) H(y/c³) = T_{j,L}(x)
  have h1 := G_mod_three_all y
  have h2 : ∑ c ∈ Icc 1 (icbrt y), μ c * (H (y / c ^ 3) : ℤ)
      ≡ ∑ c ∈ Icc 1 (icbrt y), (cL L c : ℤ) * H (y / c ^ 3) [ZMOD 3] := by
    refine Int.ModEq.sum fun c hc => ?_
    rw [mem_Icc] at hc
    have hcx : c ≤ icbrt x := le_icbrt ((cube_le_iff.2 hc.2).trans hyx)
    have := N4_pointwise L (n := c) hc.1 (lt_of_le_of_lt hcx hL)
    exact ((ZMod.intCast_eq_intCast_iff _ _ 3).1 this.symm).mul_right _
  have h3 : ∑ c ∈ Icc 1 (icbrt y), (cL L c : ℤ) * H (y / c ^ 3) = (TT j L x : ℤ) := by
    rw [TT_eq hj1]
    apply sum_subset
    · intro c hc
      rw [mem_Icc] at hc ⊢
      exact ⟨hc.1, hc.2.trans ((icbrt_le y).trans hyx)⟩
    · intro c hc1 hc
      rw [mem_Icc] at hc1 hc
      have : y / c ^ 3 = 0 := by
        apply Nat.div_eq_of_lt
        by_contra h; push Not at h
        exact hc ⟨hc1.1, cube_le_iff.1 h⟩
      rw [this, H_zero]; simp
  have := (h1.trans h2).trans (modEq_of_eq h3)
  calc (μ j : ℤ) * j * Gpp y = ((j : ℤ) * μ j) * Gpp y := by ring
    _ ≡ wN j * (TT j L x : ℤ) [ZMOD 3] := hw.symm.mul this

/-- **(N5) over `ℤ/3`**, with the weights `j μ(j)`. -/
theorem N5_zmod (x L : ℕ) (hL : icbrt x < 2 ^ (3 ^ L)) :
    (Nat.primeCounting x : ZMod 3)
      = ∑ j ∈ Icc 1 (Nat.log 2 x), (((j : ℤ) * μ j : ℤ) : ZMod 3) * (TT j L x : ZMod 3) := by
  have := (ZMod.intCast_eq_intCast_iff _ _ 3).2 (N5 x L hL)
  push_cast at this
  rw [this]
  refine sum_congr rfl fun j _ => ?_
  have h : (((j : ℤ) * μ j % 3 : ℤ) : ZMod 3) = (((j : ℤ) * μ j : ℤ) : ZMod 3) :=
    (ZMod.intCast_eq_intCast_iff _ _ 3).2 (Int.mod_modEq _ _)
  rw [wN, h]

/-- A depth that works: `L = ⌈log₃ (log₂ x)⌉`-type, e.g. any `L` with `x < 2^(3^L)`. -/
theorem depth_ok {x L : ℕ} (h : x < 2 ^ (3 ^ L)) : icbrt x < 2 ^ (3 ^ L) :=
  lt_of_le_of_lt (icbrt_le x) h

end M2L5
