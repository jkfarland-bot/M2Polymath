module

public import Mathlib
public import Found
public import DirBase
public import DirMain
public import Moment
public import MomentZ

/-!
Run r25 / M2, seat M2L: the slice link (Theorem A of A19, integer case) and the
arithmetic-function forms of Theorem B and of the Theorem H lower bound.

Setting: `ArithmeticFunction ℤ`. A family member is
`fam T c G h = sum over z in T of c z * (G z * h z)` (Dirichlet products, pointwise sum), where
`G z` is multiplicative with `G z (q) = z` at the relevant primes (for example `zeta ^ z`,
or `moebius ^ |z|` for negative `z`: `zpowZeta`) and `h z` vanishes on squarefree `n > 1`.
Twists are covered by congruences: `G z (q) = z (mod N)` only for primes `q` in a set `P`.

Contents.
1. `fam_slice`: if `n` is squarefree with all prime factors in `P`, then
   `fam n = sum over z of c z * h z 1 * z ^ omega(n) (mod N)`; `fam_slice_exact` (untwisted,
   `N = 0`): equality.
2. `zpowZeta z`: `zeta ^ z` for `z >= 0`, `moebius ^ |z|` for `z < 0`; multiplicative, value `z`
   at every prime.
3. `TargetD p v k f`: at every prime `q`, `f q = p^v u_q (mod p^(v+k))` with `p` not dividing
   `u_q`; `f n = 0 (mod p^(v+k))` whenever `omega(n) >= 2`.
4. `thmH_arith` (twisted) and `thmH_arith_zpow` (untwisted): `TargetD` forces
   `k <= sum over z in T of v_p(z)`; `cheap_arith_lower`, `signed_arith_lower`: `S(p^k) <= Z`
   for nodes in `{1..Z}`, `S(p^ceil(k/2)) <= Z` for nodes in `{-Z..-1} union {1..Z}`.
5. `thmB_arith` (twisted), `thmB_arith_exists`: `TargetD p 1 1` (target D) forces
   `sum over v_p(z) = 1 of c_z h_z(1) (z / p) = u (mod p)` and a node with `v_p(z) = 1` whose
   aggregated coefficient `c_z h_z(1)` is prime to `p`.

Lean v4.35.0-rc2 with Mathlib v4.35.0-rc2 (module system); imports DirBase (r25 library: `mapHom`, `pow_apply_one`), DirMain
(`mul_apply_prime`), Moment, MomentZ. No sorry.
-/

@[expose] public section

namespace M2L

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-! ## 1. Multiplicative functions on squarefree arguments -/

section Squarefree

variable {R : Type*} [CommRing R]

theorem omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- A multiplicative function with value `w` at every prime factor of a squarefree `n` takes the
value `w ^ omega(n)` at `n`. -/
theorem apply_squarefree_of_mult {G : ArithmeticFunction R} (hG : G.IsMultiplicative) {n : ℕ}
    (hn : Squarefree n) {w : R} (hw : ∀ q, q.Prime → q ∣ n → G q = w) : G n = w ^ ω n := by
  have e := Nat.prod_primeFactors_of_squarefree hn
  rw [← e, hG.map_prod_of_subset_primeFactors n _ subset_rfl, e, omega_eq_card,
    ← prod_const]
  apply prod_congr rfl
  intro q hq
  have := Nat.mem_primeFactors.mp hq
  exact hw q this.1 this.2.1

/-- If `h` vanishes on squarefree `m > 1`, then `(G * h)(n) = G(n) h(1)` on squarefree `n`. -/
theorem mul_apply_squarefree (G h : ArithmeticFunction R) {n : ℕ} (hn : Squarefree n)
    (hh : ∀ m, Squarefree m → 1 < m → h m = 0) : (G * h) n = G n * h 1 := by
  have hn0 : n ≠ 0 := hn.ne_zero
  rw [mul_apply, sum_eq_single (n, 1)]
  · intro x hx hne
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h2 : x.2 ≠ 1 := by
      intro h1
      apply hne
      refine Prod.ext ?_ h1
      rw [← hx'.1, h1, mul_one]
    have h20 : x.2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hx'; exact hx'.2 hx'.1.symm
    have hsq : Squarefree x.2 := hn.squarefree_of_dvd ⟨x.1, by rw [← hx'.1, mul_comm]⟩
    rw [hh x.2 hsq (by omega), mul_zero]
  · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn0⟩) h

theorem isMultiplicative_mapHom {S : Type*} [CommRing S] (φ : R →+* S)
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    (FrobLevel.Dir.mapHom φ f).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · rw [FrobLevel.Dir.mapHom_apply, hf.map_one, map_one]
  · rw [FrobLevel.Dir.mapHom_apply, FrobLevel.Dir.mapHom_apply, FrobLevel.Dir.mapHom_apply,
      hf.map_mul_of_coprime hmn, map_mul]

end Squarefree

/-! ## 2. The family and the slice formula -/

/-- The family member `sum over z in T of c z * (G z * h z)`. -/
def fam (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => ∑ z ∈ T, c z * (G z * h z) n, by simp⟩

theorem fam_apply (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ) (n : ℕ) :
    fam T c G h n = ∑ z ∈ T, c z * (G z * h z) n := rfl

/-- The aggregated coefficient `a_z = c_z h_z(1)`. -/
def agg (c : ℤ → ℤ) (h : ℤ → ArithmeticFunction ℤ) : ℤ → ℤ := fun z => c z * h z 1

/-- **Slice formula (Theorem A, integer case).** Let `n` be squarefree. If every `G z` is
multiplicative with `G z (q) = z (mod N)` at the prime factors `q` of `n`, and every `h z` is
`0 (mod N)` on squarefree `m > 1`, then `fam n = sum over z of c z h z(1) z ^ omega(n) (mod N)`. -/
theorem fam_slice (N : ℕ) (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ)
    (hG : ∀ z ∈ T, (G z).IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    (hGq : ∀ z ∈ T, ∀ q, q.Prime → q ∣ n → (N : ℤ) ∣ G z q - z)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → (N : ℤ) ∣ h z m) :
    (N : ℤ) ∣ fam T c G h n - mom T (agg c h) (ω n) := by
  let φ := Int.castRingHom (ZMod N)
  have hφ : ∀ x y : ℤ, (N : ℤ) ∣ x - y ↔ φ x = φ y := fun x y => by
    rw [eq_comm]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub y x N).symm
  rw [hφ, fam_apply, mom, map_sum, map_sum]
  apply sum_congr rfl
  intro z hz
  have h1 : φ ((G z * h z) n) =
      (FrobLevel.Dir.mapHom φ (G z) * FrobLevel.Dir.mapHom φ (h z)) n := by
    rw [← map_mul]; rfl
  have hh' : ∀ m, Squarefree m → 1 < m → FrobLevel.Dir.mapHom φ (h z) m = 0 := by
    intro m hm hm1
    rw [FrobLevel.Dir.mapHom_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 (hh z hz m hm hm1)
  have hG' : ∀ q, q.Prime → q ∣ n → FrobLevel.Dir.mapHom φ (G z) q = φ z := by
    intro q hq hqn
    rw [FrobLevel.Dir.mapHom_apply]
    exact ((hφ _ _).1 (hGq z hz q hq hqn))
  rw [map_mul, h1, mul_apply_squarefree _ _ hn hh',
    apply_squarefree_of_mult (isMultiplicative_mapHom φ (hG z hz)) hn hG',
    FrobLevel.Dir.mapHom_apply, agg, map_mul, map_mul, map_pow]
  ring

/-- **Slice formula, untwisted (exact).** With `G z (q) = z` at the prime factors of the
squarefree `n` and `h z = 0` on squarefree `m > 1`: `fam n = s_omega(n)` exactly, where
`s_r = sum over z of c z h z(1) z^r`. -/
theorem fam_slice_exact (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ)
    (hG : ∀ z ∈ T, (G z).IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    (hGq : ∀ z ∈ T, ∀ q, q.Prime → q ∣ n → G z q = z)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0) :
    fam T c G h n = mom T (agg c h) (ω n) := by
  have := fam_slice 0 T c G h hG hn (fun z hz q hq hqn => by simp [hGq z hz q hq hqn])
    (fun z hz m hm hm1 => by simp [hh z hz m hm hm1])
  rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at this
  exact this

/-- Squarefree slices: for an infinite set `P` of primes and every `r`, a squarefree `n` with
`omega(n) = r` and all prime factors in `P`. -/
theorem exists_slice (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime) (r : ℕ) :
    ∃ n, Squarefree n ∧ ω n = r ∧ ∀ q, q.Prime → q ∣ n → q ∈ P := by
  obtain ⟨S, hSP, hS⟩ := hP.exists_subset_card_eq r
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => hPp q (hSP hq)
  have hpf := Nat.primeFactors_prod hSp
  refine ⟨∏ q ∈ S, q, ?_, ?_, ?_⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hSp a ha) (hSp b hb)).2 hab)
    · intro q hq
      exact (hSp q hq).prime.irreducible.squarefree
  · rw [omega_eq_card, hpf, hS]
  · intro q hq hqn
    have hne : ∏ q ∈ S, q ≠ 0 := prod_ne_zero_iff.mpr fun q hq => (hSp q hq).ne_zero
    have : q ∈ (∏ q ∈ S, q).primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hne⟩
    rw [hpf] at this
    exact hSP this

/-! ## 3. The untwisted cores `zeta ^ z` and `moebius ^ |z|` -/

/-- The core of signed degree `z`: `zeta ^ z` for `z >= 0`, `moebius ^ |z|` for `z < 0`. -/
noncomputable def zpowZeta (z : ℤ) : ArithmeticFunction ℤ :=
  if 0 ≤ z then (ζ : ArithmeticFunction ℤ) ^ z.toNat else (μ : ArithmeticFunction ℤ) ^ z.natAbs

theorem pow_apply_prime' {F : ArithmeticFunction ℤ} (hF : F 1 = 1) (m : ℕ) {q : ℕ}
    (hq : q.Prime) : (F ^ m) q = m * F q := by
  induction m with
  | zero => simp [ArithmeticFunction.one_apply_ne hq.one_lt.ne']
  | succ m ih =>
    rw [pow_succ, FrobLevel.Dir.mul_apply_prime _ _ hq, ih, FrobLevel.Dir.pow_apply_one, hF,
      one_pow]
    push_cast; ring

theorem zeta_int_one : (ζ : ArithmeticFunction ℤ) 1 = 1 := by simp

theorem zeta_int_prime {q : ℕ} (hq : q.Prime) : (ζ : ArithmeticFunction ℤ) q = 1 := by
  simp [hq.ne_zero]

theorem zpowZeta_mult (z : ℤ) : (zpowZeta z).IsMultiplicative := by
  unfold zpowZeta
  split_ifs
  · exact isMultiplicative_zeta.natCast.pow
  · exact isMultiplicative_moebius.pow

theorem zpowZeta_prime (z : ℤ) {q : ℕ} (hq : q.Prime) : zpowZeta z q = z := by
  unfold zpowZeta
  split_ifs with hz
  · rw [pow_apply_prime' zeta_int_one _ hq, zeta_int_prime hq, mul_one]; omega
  · rw [pow_apply_prime' (by simp) _ hq, moebius_apply_prime hq]; omega

theorem zpowZeta_of_pos {z : ℤ} (hz : 0 ≤ z) : zpowZeta z = (ζ : ArithmeticFunction ℤ) ^ z.toNat := by
  rw [zpowZeta, ite_eq_left hz]

/-! ## 4. The target and Theorem H (lower bound) for arithmetic functions -/

section Targets

variable (p : ℕ) [hp : Fact p.Prime]

/-- Target `D_k` with offset `v`: at every prime `q`, `f q = p^v u_q (mod p^(v+k))` with `p` not
dividing `u_q`; and `f n = 0 (mod p^(v+k))` whenever `omega(n) >= 2`. (The value at `1` and
at higher prime powers is free.) -/
def TargetD (v k : ℕ) (f : ArithmeticFunction ℤ) : Prop :=
  (∀ q : ℕ, q.Prime → ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ^ (v + k) ∣ f q - p ^ v * u) ∧
    ∀ n : ℕ, 2 ≤ ω n → (p : ℤ) ^ (v + k) ∣ f n

omit hp in
theorem natCast_pow_int (v k : ℕ) : (((p ^ (v + k) : ℕ)) : ℤ) = (p : ℤ) ^ (v + k) := by
  push_cast; ring

omit hp in
/-- The moment target from the arithmetic target, along an infinite set `P` of primes
on which the cores are `z (mod p^(v+k))`. -/
theorem momentTarget_of_targetD {v k : ℕ} (T : Finset ℤ) (c : ℤ → ℤ)
    (G h : ℤ → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ z ∈ T, (G z).IsMultiplicative)
    (hGq : ∀ z ∈ T, ∀ q ∈ P, (p : ℤ) ^ (v + k) ∣ G z q - z)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h z m)
    (hf : TargetD p v k (fam T c G h)) :
    (∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ^ (v + k) ∣ mom T (agg c h) 1 - p ^ v * u) ∧
      ∀ r, 2 ≤ r → (p : ℤ) ^ (v + k) ∣ mom T (agg c h) r := by
  have hsl : ∀ n, Squarefree n → (∀ q, q.Prime → q ∣ n → q ∈ P) →
      (p : ℤ) ^ (v + k) ∣ fam T c G h n - mom T (agg c h) (ω n) := by
    intro n hn hnP
    have := fam_slice (p ^ (v + k)) T c G h hG hn
      (fun z hz q hq hqn => by rw [natCast_pow_int]; exact hGq z hz q (hnP q hq hqn))
      (fun z hz m hm hm1 => by rw [natCast_pow_int]; exact hh z hz m hm hm1)
    rwa [natCast_pow_int] at this
  constructor
  · obtain ⟨q, hqP⟩ := hP.nonempty
    have hq := hPp q hqP
    obtain ⟨u, hu, hfu⟩ := hf.1 q hq
    have hs := hsl q hq.prime.irreducible.squarefree (fun q' hq' hq'q => by
      rw [(Nat.prime_dvd_prime_iff_eq hq' hq).1 hq'q]; exact hqP)
    rw [cardDistinctFactors_apply_prime hq] at hs
    refine ⟨u, hu, ?_⟩
    have := dvd_sub hfu hs
    rwa [sub_sub_sub_cancel_left] at this
  · intro r hr
    obtain ⟨n, hn, hnr, hnP⟩ := exists_slice P hP hPp r
    have hs := hsl n hn hnP
    rw [hnr] at hs
    have := dvd_sub (hf.2 n (hnr ▸ hr)) hs
    rwa [sub_sub_cancel] at this

/-- **Theorem H, lower bound (arithmetic functions, with twists).** Nodes `T` without `0`;
cores `G z` multiplicative with `G z (q) = z (mod p^(v+k))` for `q` in an infinite set `P` of
primes; corrections `h z = 0 (mod p^(v+k))` on squarefree `m > 1`. If
`fam T c G h` meets `TargetD p v k`, then `k <= sum over z in T of v_p(z)`. -/
theorem thmH_arith {v k : ℕ} (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (c : ℤ → ℤ)
    (G h : ℤ → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ z ∈ T, (G z).IsMultiplicative)
    (hGq : ∀ z ∈ T, ∀ q ∈ P, (p : ℤ) ^ (v + k) ∣ G z q - z)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (v + k) ∣ h z m)
    (hf : TargetD p v k (fam T c G h)) :
    k ≤ ∑ z ∈ T, padicValInt p z := by
  obtain ⟨⟨u, hu, h1⟩, hr⟩ := momentTarget_of_targetD p T c G h P hP hPp hG hGq hh hf
  exact thmH_moment p T h0 (agg c h) v k u hu h1 (fun r hr2 _ => hr r hr2)

/-- **Theorem H, lower bound, untwisted.** Cores `zpowZeta z` (`zeta ^ z`, or `moebius ^ |z|`
for negative `z`), corrections `h z` vanishing on squarefree `m > 1`. -/
theorem thmH_arith_zpow {v k : ℕ} (T : Finset ℤ) (h0 : (0 : ℤ) ∉ T) (c : ℤ → ℤ)
    (h : ℤ → ArithmeticFunction ℤ) (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0)
    (hf : TargetD p v k (fam T c zpowZeta h)) :
    k ≤ ∑ z ∈ T, padicValInt p z :=
  thmH_arith p T h0 c zpowZeta h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq)
    (fun z _ => zpowZeta_mult z)
    (fun z _ q hq => by rw [zpowZeta_prime z hq, sub_self]; exact dvd_zero _)
    (fun z hz m hm hm1 => by rw [hh z hz m hm hm1]; exact dvd_zero _) hf

/-- **Cheap lower bound (arithmetic functions).** Nodes in `{1..Z}`, cores `zeta ^ z`: if the
family member meets `TargetD p v k`, then `S(p^k) <= Z`. -/
theorem cheap_arith_lower {v k Z : ℕ} (T : Finset ℤ) (hT : T ⊆ cheapNodes Z) (c : ℤ → ℤ)
    (h : ℤ → ArithmeticFunction ℤ) (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0)
    (hf : TargetD p v k (fam T c zpowZeta h)) : FrobLevel.kempner p k ≤ Z := by
  have h1 := thmH_arith_zpow p T (fun h => zero_not_mem_cheap Z (hT h)) c h hh hf
  have h2 : ∑ z ∈ T, padicValInt p z ≤ ∑ z ∈ cheapNodes Z, padicValInt p z :=
    sum_le_sum_of_subset hT
  rw [sum_val_cheap] at h2
  exact FrobLevel.kempner_le p (h1.trans h2)

/-- **Signed lower bound (arithmetic functions).** Nodes in `{-Z..-1} union {1..Z}`, cores
`zeta ^ z` and `moebius ^ |z|`: if the family member meets `TargetD p v k`, then
`S(p^ceil(k/2)) <= Z`. -/
theorem signed_arith_lower {v k Z : ℕ} (T : Finset ℤ) (hT : T ⊆ signedNodes Z) (c : ℤ → ℤ)
    (h : ℤ → ArithmeticFunction ℤ) (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0)
    (hf : TargetD p v k (fam T c zpowZeta h)) : FrobLevel.kempner p ((k + 1) / 2) ≤ Z := by
  have h1 := thmH_arith_zpow p T (fun h => zero_not_mem_signed Z (hT h)) c h hh hf
  have h2 : ∑ z ∈ T, padicValInt p z ≤ ∑ z ∈ signedNodes Z, padicValInt p z :=
    sum_le_sum_of_subset hT
  rw [sum_val_signed] at h2
  exact FrobLevel.kempner_le p (by omega)

/-! ## 5. Theorem B for arithmetic functions -/

/-- **Theorem B (arithmetic functions, with twists, exact form).** Target D is
`TargetD p 1 1`: prime values `p u_q (mod p^2)` with `p` not dividing `u_q`, and `0 (mod p^2)`
on `omega >= 2`. Cores `G z (q) = z (mod p^2)` on an infinite set `P` of primes, corrections
`0 (mod p^2)` on squarefree `m > 1`. Then for every `q` in `P` and every `u` with
`f q = p u (mod p^2)`: `sum over nodes z with v_p(z) = 1 of c_z h_z(1) (z / p) = u (mod p)`. -/
theorem thmB_arith (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ) (P : Set ℕ)
    (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime) (hG : ∀ z ∈ T, (G z).IsMultiplicative)
    (hGq : ∀ z ∈ T, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G z q - z)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h z m)
    (hf : TargetD p 1 1 (fam T c G h)) {q : ℕ} (hqP : q ∈ P) {u : ℤ}
    (hu : (p : ℤ) ^ 2 ∣ fam T c G h q - p * u) :
    (p : ℤ) ∣ ∑ z ∈ val1 p T, agg c h z * (z / p) - u := by
  have hq := hPp q hqP
  have hs := fam_slice (p ^ 2) T c G h hG hq.prime.irreducible.squarefree
    (fun z hz q' hq' hq'q => by
      push_cast; exact hGq z hz q' ((Nat.prime_dvd_prime_iff_eq hq' hq).1 hq'q ▸ hqP))
    (fun z hz m hm hm1 => by push_cast; exact hh z hz m hm hm1)
  push_cast at hs
  rw [cardDistinctFactors_apply_prime hq] at hs
  have h1 : (p : ℤ) ^ 2 ∣ mom T (agg c h) 1 - p * u := by
    have := dvd_sub hu hs
    rwa [sub_sub_sub_cancel_left] at this
  have h2 := hp.out.two_le
  have hr1 : 1 ≤ p * (p - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hP2 : ∀ z ∈ T, ∀ q ∈ P, (p : ℤ) ^ (1 + 1) ∣ G z q - z := fun z hz q hq => hGq z hz q hq
  have hh2 : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ (1 + 1) ∣ h z m := hh
  obtain ⟨_, hr⟩ := momentTarget_of_targetD p T c G h P hP hPp hG hP2 hh2 hf
  exact thmB_moment p T (agg c h) u (r := 1 + p * (p - 1)) (by omega) (by simp) h1
    (hr _ (by omega))

/-- **Theorem B (arithmetic functions, existence).** Under target D, some node `z` with
`v_p(z) = 1` has aggregated coefficient `c_z h_z(1)` prime to `p`. -/
theorem thmB_arith_exists (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ)
    (P : Set ℕ) (hP : P.Infinite) (hPp : ∀ q ∈ P, q.Prime)
    (hG : ∀ z ∈ T, (G z).IsMultiplicative)
    (hGq : ∀ z ∈ T, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G z q - z)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h z m)
    (hf : TargetD p 1 1 (fam T c G h)) :
    ∃ z ∈ T, (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧ ¬ (p : ℤ) ∣ agg c h z := by
  obtain ⟨q, hqP⟩ := hP.nonempty
  obtain ⟨u, hu, hfu⟩ := hf.1 q (hPp q hqP)
  have hfu' : (p : ℤ) ^ 2 ∣ fam T c G h q - p * u := by simpa using hfu
  have key := thmB_arith p T c G h P hP hPp hG hGq hh hf hqP hfu'
  by_contra hne
  push Not at hne
  have hall : (p : ℤ) ∣ ∑ z ∈ val1 p T, agg c h z * (z / p) := dvd_sum fun z hz => by
    have hz' := mem_filter.mp hz
    exact (hne z hz'.1 hz'.2.1 hz'.2.2).mul_right _
  exact hu (by have := dvd_sub hall key; rwa [sub_sub_cancel] at this)

/-- **Theorem B, untwisted.** Cores `zpowZeta z`, corrections vanishing on squarefree `m > 1`. -/
theorem thmB_arith_zpow_exists (T : Finset ℤ) (c : ℤ → ℤ) (h : ℤ → ArithmeticFunction ℤ)
    (hh : ∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0)
    (hf : TargetD p 1 1 (fam T c zpowZeta h)) :
    ∃ z ∈ T, (p : ℤ) ∣ z ∧ ¬ (p : ℤ) ^ 2 ∣ z ∧ ¬ (p : ℤ) ∣ agg c h z :=
  thmB_arith_exists p T c zpowZeta h {q | q.Prime} Nat.infinite_setOfPred_prime (fun _ hq => hq)
    (fun z _ => zpowZeta_mult z)
    (fun z _ q hq => by rw [zpowZeta_prime z hq, sub_self]; exact dvd_zero _)
    (fun z hz m hm hm1 => by rw [hh z hz m hm hm1]; exact dvd_zero _) hf

end Targets

end M2L
