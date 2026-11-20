/-
  Seat M2L4, item 5b: Result N's identity (N4) (A19 section 9b) for the coefficients
  c_0 = δ, c_{L+1} = d_2 * E_3(c_L):  c_L ≡ μ * E_{3^L}(ζ) (mod 3), hence c_L(n) ≡ μ(n) (mod 3)
  for 1 ≤ n < 2^(3^L), with first failure at n = 2^(3^L) (difference 1 mod 3).
  Ingredients: the dilation E_k as a multiplicative map of Dirichlet rings, and the Frobenius
  identity ζ^3 = E_3(ζ) over Z/3.
-/
import Mathlib
import M2ResultM
import M2Polymath

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace M2L4
open M2L3

/-! ## The dilation `E_k` -/

section Dilation

variable {R : Type*} [CommSemiring R]

lemma iroot_zero (k : ℕ) : iroot k 0 = 0 := by simp [iroot]

lemma iroot_pow_self {k : ℕ} (hk : 0 < k) (c : ℕ) : iroot k (c ^ k) = c := by
  apply le_antisymm
  · have := iroot_pow_le hk (c ^ k)
    exact (Nat.pow_le_pow_iff_left hk.ne').1 this
  · exact (pow_le_iff_le_iroot hk).1 le_rfl

/-- `E_k(f)(n) = f(m)` if `n = m^k`, and `0` if `n` is not a `k`-th power. -/
def Ek (k : ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => if iroot k n ^ k = n then f (iroot k n) else 0, by
    simp only [iroot_zero]; split_ifs <;> simp⟩

lemma Ek_apply (k : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    Ek k f n = if iroot k n ^ k = n then f (iroot k n) else 0 := rfl

lemma Ek_pow {k : ℕ} (hk : 0 < k) (f : ArithmeticFunction R) (c : ℕ) : Ek k f (c ^ k) = f c := by
  rw [Ek_apply, iroot_pow_self hk, if_pos rfl]

lemma Ek_notpow {k : ℕ} (f : ArithmeticFunction R) {n : ℕ} (h : ∀ c, c ^ k ≠ n) : Ek k f n = 0 := by
  rw [Ek_apply, if_neg (h _)]

lemma Ek_one_fun (f : ArithmeticFunction R) : Ek 1 f = f := by
  ext n; rw [Ek_apply, iroot_one, pow_one, if_pos rfl]

lemma pow_left_inj' {k : ℕ} (hk : 0 < k) {a b : ℕ} (h : a ^ k = b ^ k) : a = b :=
  Nat.pow_left_injective hk.ne' h

/-- `E_k` is multiplicative for the Dirichlet product: `E_k(f * g) = E_k(f) * E_k(g)`. -/
theorem Ek_mul {k : ℕ} (hk : 0 < k) (f g : ArithmeticFunction R) :
    Ek k (f * g) = Ek k f * Ek k g := by
  ext n
  by_cases hn : ∃ m, m ^ k = n
  · obtain ⟨m, rfl⟩ := hn
    rw [Ek_pow hk, mul_apply, mul_apply]
    refine sum_bij_ne_zero (fun x _ _ => (x.1 ^ k, x.2 ^ k)) ?_ ?_ ?_ ?_
    · intro x hx _
      rw [Nat.mem_divisorsAntidiagonal] at hx ⊢
      exact ⟨by rw [← mul_pow, hx.1], pow_ne_zero _ hx.2⟩
    · intro x _ _ y _ _ hxy
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (pow_left_inj' hk hxy.1) (pow_left_inj' hk hxy.2)
    · intro y hy hne
      rw [Nat.mem_divisorsAntidiagonal] at hy
      by_cases h1 : ∃ c, c ^ k = y.1
      · by_cases h2 : ∃ d, d ^ k = y.2
        · obtain ⟨c, hc⟩ := h1
          obtain ⟨d, hd⟩ := h2
          have hcd : c * d = m := pow_left_inj' hk (by rw [mul_pow, hc, hd, hy.1])
          have hm : m ≠ 0 := by rintro rfl; exact hy.2 (by simp [Nat.zero_pow hk])
          refine ⟨(c, d), Nat.mem_divisorsAntidiagonal.2 ⟨hcd, hm⟩, ?_, ?_⟩
          · intro h0; apply hne; rw [← hc, ← hd, Ek_pow hk, Ek_pow hk]
            exact h0
          · exact Prod.ext hc hd
        · exact absurd (by rw [Ek_notpow g (fun d hd => h2 ⟨d, hd⟩), mul_zero]) hne
      · exact absurd (by rw [Ek_notpow f (fun c hc => h1 ⟨c, hc⟩), zero_mul]) hne
    · intro x _ _
      simp only [Ek_pow hk]
  · rw [Ek_notpow _ (fun c hc => hn ⟨c, hc⟩), mul_apply]
    symm
    refine sum_eq_zero fun y hy => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hy
    by_cases h1 : ∃ c, c ^ k = y.1
    · by_cases h2 : ∃ d, d ^ k = y.2
      · obtain ⟨c, hc⟩ := h1
        obtain ⟨d, hd⟩ := h2
        exact absurd ⟨c * d, by rw [mul_pow, hc, hd, hy.1]⟩ hn
      · rw [Ek_notpow g (fun d hd => h2 ⟨d, hd⟩), mul_zero]
    · rw [Ek_notpow f (fun c hc => h1 ⟨c, hc⟩), zero_mul]

theorem Ek_one {k : ℕ} (hk : 0 < k) : Ek k (1 : ArithmeticFunction R) = 1 := by
  ext n
  by_cases hn : ∃ m, m ^ k = n
  · obtain ⟨m, rfl⟩ := hn
    rw [Ek_pow hk]
    by_cases hm : m = 1
    · subst hm; simp
    · rw [one_apply_ne hm, one_apply_ne]
      intro h; exact hm (pow_left_inj' hk (by rw [h, one_pow]))
  · rw [Ek_notpow _ (fun c hc => hn ⟨c, hc⟩), one_apply_ne]
    rintro rfl; exact hn ⟨1, one_pow k⟩

/-- `E_a ∘ E_b = E_{b a}`. -/
theorem Ek_Ek {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (f : ArithmeticFunction R) :
    Ek a (Ek b f) = Ek (b * a) f := by
  ext n
  by_cases hn : ∃ l, l ^ (b * a) = n
  · obtain ⟨l, rfl⟩ := hn
    rw [pow_mul, Ek_pow ha, Ek_pow hb, ← pow_mul, Ek_pow (Nat.mul_pos hb ha)]
  · rw [Ek_notpow _ (fun c hc => hn ⟨c, hc⟩)]
    by_cases hc : ∃ c, c ^ a = n
    · obtain ⟨c, rfl⟩ := hc
      rw [Ek_pow ha, Ek_notpow]
      rintro l rfl; exact hn ⟨l, by rw [pow_mul]⟩
    · rw [Ek_notpow _ (fun c h => hc ⟨c, h⟩)]

/-- `E_k` preserves multiplicativity. -/
theorem isMultiplicative_Ek {k : ℕ} (hk : 0 < k) {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) : IsMultiplicative (Ek k f) := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [← one_pow k, Ek_pow hk]; exact hf.map_one, ?_⟩
  intro m n hm hn hmn
  by_cases hcm : ∃ a, a ^ k = m
  · by_cases hcn : ∃ b, b ^ k = n
    · obtain ⟨a, rfl⟩ := hcm
      obtain ⟨b, rfl⟩ := hcn
      have hab : a.Coprime b :=
        (Nat.coprime_pow_right_iff hk _ _).1 ((Nat.coprime_pow_left_iff hk _ _).1 hmn)
      rw [← mul_pow, Ek_pow hk, Ek_pow hk, Ek_pow hk, hf.map_mul_of_coprime hab]
    · rw [Ek_notpow (n := n) _ (fun b hb => hcn ⟨b, hb⟩), mul_zero]
      apply Ek_notpow
      intro c hc
      have hu : IsUnit (gcd n m) := Nat.isUnit_iff.2 (Nat.Coprime.symm hmn)
      obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu (by rw [mul_comm]; exact hc.symm)
      exact hcn ⟨d, hd.symm⟩
  · rw [Ek_notpow (n := m) _ (fun a ha => hcm ⟨a, ha⟩), zero_mul]
    apply Ek_notpow
    intro c hc
    have hu : IsUnit (gcd m n) := Nat.isUnit_iff.2 hmn
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hu hc.symm
    exact hcm ⟨d, hd.symm⟩

/-- At a prime power: `E_k(f)(q^i) = f(q^(i/k))` if `k ∣ i`, else `0`. -/
lemma Ek_prime_pow {k : ℕ} (hk : 0 < k) (f : ArithmeticFunction R) {q : ℕ} (hq : q.Prime) (i : ℕ) :
    Ek k f (q ^ i) = if k ∣ i then f (q ^ (i / k)) else 0 := by
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hk, mul_comm, pow_mul, Ek_pow hk]
  · apply Ek_notpow
    intro c hc
    have hcd : c ∣ q ^ i := hc ▸ dvd_pow_self c hk.ne'
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hcd
    rw [← pow_mul] at hc
    exact h ⟨j, by rw [mul_comm]; exact Nat.pow_right_injective hq.two_le hc.symm⟩

end Dilation

/-! ## Over `ℤ/3`: Frobenius and (N4) -/

/-- `ζ` and `μ` with values in `ℤ/3`. -/
noncomputable abbrev ζ3 : ArithmeticFunction (ZMod 3) :=
  (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod 3))
noncomputable abbrev μ3 : ArithmeticFunction (ZMod 3) := ((μ : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod 3))

lemma μ3_mul_ζ3 : μ3 * ζ3 = 1 := by
  rw [← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]

lemma ζ3_mult : IsMultiplicative ζ3 := isMultiplicative_zeta.natCast.intCast

lemma zmod3_d3 : ∀ x d : ZMod 3, 2 * d = (x + 1) * (x + 2) → d = if x = 0 then 1 else 0 := by
  decide

/-- **Frobenius over `ℤ/3`**: `ζ * ζ * ζ = E_3(ζ)`, i.e. `d_3(n) ≡ [n is a cube] (mod 3)`. -/
theorem zeta_cube_frobenius : ζ3 * ζ3 * ζ3 = Ek 3 ζ3 := by
  have hd : ζ3 * ζ3 * ζ3 = (((d3 : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod 3)) := by
    simp only [d3, natCoe_mul, intCoe_mul]
  rw [hd]
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ ?_ _ (isMultiplicative_Ek (by norm_num) ζ3_mult)).2 ?_
  · exact (isMultiplicative_d3).natCast.intCast
  intro q i hq
  rw [Ek_prime_pow (by norm_num) _ hq, intCoe_apply, natCoe_apply]
  have h2 := d3_prime_pow_two_mul hq i
  have hc : (2 : ZMod 3) * ((d3 (q ^ i) : ℕ) : ZMod 3) = ((i : ℕ) + 1 : ZMod 3) * ((i : ℕ) + 2) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ZMod 3)) h2
  have := zmod3_d3 _ _ hc
  push_cast
  rw [this]
  by_cases h3 : 3 ∣ i
  · rw [if_pos ((ZMod.natCast_eq_zero_iff i 3).2 h3), if_pos h3]
    simp [ζ3, natCoe_apply, hq.ne_zero]
  · rw [if_neg (fun h => h3 ((ZMod.natCast_eq_zero_iff i 3).1 h)), if_neg h3]

/-- `d_2 = ζ * ζ` over `ℤ`. -/
noncomputable def d2Z : ArithmeticFunction ℤ := (ζ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)

/-- **Result N's coefficients**: `c_0 = δ`, `c_{L+1} = d_2 * E_3(c_L)`. -/
noncomputable def cL : ℕ → ArithmeticFunction ℤ
  | 0 => 1
  | L + 1 => d2Z * Ek 3 (cL L)

lemma intCoe_Ek (k : ℕ) (f : ArithmeticFunction ℤ) :
    ((Ek k f : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod 3)) = Ek k (f : ArithmeticFunction (ZMod 3)) := by
  ext n; rw [intCoe_apply, Ek_apply, Ek_apply]; split_ifs <;> simp [intCoe_apply]

/-- **(N4)**: `c_L ≡ μ * E_{3^L}(ζ) (mod 3)` as arithmetic functions, for every depth `L`. -/
theorem N4 (L : ℕ) :
    ((cL L : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod 3)) = μ3 * Ek (3 ^ L) ζ3 := by
  induction L with
  | zero => rw [cL, intCoe_one, pow_zero, Ek_one_fun, μ3_mul_ζ3]
  | succ L ih =>
    have hd2 : ((d2Z : ArithmeticFunction ℤ) : ArithmeticFunction (ZMod 3)) = ζ3 * ζ3 := by
      rw [d2Z, intCoe_mul]
    have key : ζ3 * ζ3 * Ek 3 μ3 = μ3 := by
      calc ζ3 * ζ3 * Ek 3 μ3 = ζ3 * ζ3 * Ek 3 μ3 * (μ3 * ζ3) := by rw [μ3_mul_ζ3, mul_one]
        _ = (ζ3 * ζ3 * ζ3) * Ek 3 μ3 * μ3 := by ring
        _ = Ek 3 (ζ3 * μ3) * μ3 := by rw [zeta_cube_frobenius, Ek_mul (by norm_num)]
        _ = μ3 := by rw [mul_comm ζ3, μ3_mul_ζ3, Ek_one (by norm_num), one_mul]
    rw [cL, intCoe_mul, hd2, intCoe_Ek, ih, Ek_mul (by norm_num), Ek_Ek (by norm_num) (by positivity),
      ← pow_succ, ← mul_assoc, key]

lemma Ek_zeta_ne_zero {L n : ℕ} (h : Ek (3 ^ L) ζ3 n ≠ 0) : ∃ d, d ^ (3 ^ L) = n := by
  by_contra hc; push Not at hc; exact h (Ek_notpow _ hc)

/-- **(N4), pointwise**: `c_L(n) ≡ μ(n) (mod 3)` for `1 ≤ n < 2^(3^L)`. -/
theorem N4_pointwise (L : ℕ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n < 2 ^ (3 ^ L)) :
    ((cL L n : ℤ) : ZMod 3) = ((μ n : ℤ) : ZMod 3) := by
  have := congrArg (fun f : ArithmeticFunction (ZMod 3) => f n) (N4 L)
  simp only [intCoe_apply] at this
  rw [this, mul_apply, sum_eq_single_of_mem (n, 1) (by simp; omega)]
  · rw [show (1 : ℕ) = 1 ^ (3 ^ L) by simp, Ek_pow (by positivity)]
    simp [intCoe_apply]
  · intro x hx hne
    rw [Nat.mem_divisorsAntidiagonal] at hx
    by_contra h0
    obtain ⟨d, hd⟩ := Ek_zeta_ne_zero (right_ne_zero_of_mul h0)
    have hx2 : x.2 ≠ 1 := fun h => hne (Prod.ext (by rw [← hx.1, h, mul_one]) h)
    have hd2 : 2 ≤ d := by
      rcases d with _ | _ | d
      · rw [zero_pow (by positivity)] at hd; rw [← hd, mul_zero] at hx; exact (hx.2 hx.1.symm).elim
      · simp at hd; exact absurd hd.symm hx2
      · omega
    have h1 : 2 ^ (3 ^ L) ≤ x.2 := hd ▸ Nat.pow_le_pow_left hd2 _
    have h2 : x.2 ≤ n := Nat.le_of_dvd (by omega) ⟨x.1, by rw [← hx.1, mul_comm]⟩
    omega

/-- **First failure** at `n = 2^(3^L)`: `c_L(n) - μ(n) ≡ 1 (mod 3)`. -/
theorem N4_first_failure (L : ℕ) :
    ((cL L (2 ^ (3 ^ L)) : ℤ) : ZMod 3) = ((μ (2 ^ (3 ^ L)) : ℤ) : ZMod 3) + 1 := by
  set n := 2 ^ (3 ^ L) with hn
  have hk : 0 < 3 ^ L := by positivity
  have := congrArg (fun f : ArithmeticFunction (ZMod 3) => f n) (N4 L)
  simp only [intCoe_apply] at this
  have hn0 : n ≠ 0 := by positivity
  have hn1 : n ≠ 1 := by
    rw [hn]; exact (Nat.one_lt_pow hk.ne' (by norm_num)).ne'
  rw [this, mul_apply, sum_eq_add_of_mem (n, 1) (1, n) (by simp [hn0]) (by simp [hn0])
    (by simp [hn1])]
  · rw [show (1 : ℕ) = 1 ^ (3 ^ L) by simp, Ek_pow hk, hn, Ek_pow hk]
    simp [intCoe_apply]
  · intro x hx hne
    rw [Nat.mem_divisorsAntidiagonal] at hx
    by_contra h0
    obtain ⟨d, hd⟩ := Ek_zeta_ne_zero (right_ne_zero_of_mul h0)
    have hx2 : x.2 ≤ n := Nat.le_of_dvd (by omega) ⟨x.1, by rw [← hx.1, mul_comm]⟩
    have hdle : d ≤ 2 := by
      by_contra hc; push Not at hc
      have := Nat.pow_lt_pow_left hc hk.ne'
      omega
    interval_cases d
    · rw [zero_pow hk.ne'] at hd; rw [← hd, mul_zero] at hx; exact hx.2 hx.1.symm
    · rw [one_pow] at hd
      exact hne.1 (Prod.ext (by rw [← hx.1, ← hd, mul_one]) hd.symm)
    · have : x.1 = 1 := by
        have h := hx.1; rw [← hd, ← hn] at h
        exact (Nat.mul_eq_right hn0).1 h
      exact hne.2 (Prod.ext this hd.symm)

end M2L4
