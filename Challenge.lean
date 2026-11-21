module

public import Mathlib

@[expose] public section

/-!
# The M2 results: exact degrees, no prime detection, the ternary identity, `π(x) mod 3`

This file is the statement surface for the Palomar registry. It imports only Mathlib, restates
every object the results are about, and states each headline result with `sorry`.
`Solution.lean` proves every statement below, with the same name and type, from the development
in `lean/` (each restated definition is shown equal to the development's own).

## Objects

* `kempner p k` is the Kempner value `S(p^k)`: the least `N` with `p^k` dividing `N!`.
* `zpowZeta z` is the Dirichlet power `ζ^z` for `z ≥ 0` and `μ^|z|` for `z < 0` (integer valued
  arithmetic functions, Dirichlet convolution).
* `fam T c G h` is the family member `∑_{z ∈ T} c_z (G_z * h_z)`; `famI` is the same with an
  arbitrary index type and a degree map.
* `TargetD p v k f` (target `D_k` with offset `v`): at every prime `q`, `f(q) ≡ p^v u_q`
  modulo `p^(v+k)` with `p ∤ u_q`; and `f(n) ≡ 0` modulo `p^(v+k)` whenever `ω(n) ≥ 2`.
* `CheapAchievable p k Z`: some member with cores `ζ^z`, `z ∈ {1, ..., Z}`, and corrections `h_z`
  vanishing on every squarefree `m > 1`, meets `TargetD p v k` for some `v`.
  `SignedAchievable p k Z`: the same with `z ∈ {-Z, ..., -1} ∪ {1, ..., Z}` (cores `μ^|z|` for
  negative `z`).
* `TargetU p k f`: `f(q) ≡ 1` modulo `p^k` at every prime `q` and `f(n) ≡ 0` modulo `p^k` on
  squarefree `n` with `ω(n) ≥ 2` (the prime indicator modulo `p^k`).
* `Bz z` is `n ↦ z^ω(n)`; `hcorr z = (zpowZeta z)⁻¹ * Bz z` is the explicit correction.
* `icbrt x = ⌊x^(1/3)⌋`, `D3 x = ∑_{n ≤ x} d_3(n)` with `d_3 = ζ * ζ * ζ`, and `H x` is the number of
  positive triples `(a, b, c)` with `a b c ≤ x`, `a ≤ b`, `a < c`.
* `piMod3` is the certified algorithm for `π(x) mod 3`: a fast computation of `D_3` by a block
  routine, then the reduction from `D_3 mod 9` to `π mod 3`.

## Results

* `exact_degree_cheap`: for a prime `p` and `k ≥ 1`, the least `Z` for which `CheapAchievable p k Z`
  holds is `S(p^k)`.
* `exact_degree_signed`: for a prime `p` and `k ≥ 1`, the least `Z` for which
  `SignedAchievable p k Z` holds is `S(p^⌈k/2⌉)`.
* `no_prime_detection` (Corollary A1): for `k ≥ 1`, no member of the untwisted family (multiplicative
  cores whose value at every prime is the integer degree, corrections vanishing on squarefree
  `m > 1`, any integer coefficients) gives the prime indicator modulo `p^k`.
* `degree_p_needed`: with degrees in `{0, ..., p - 1}` (cores congruent to their degree modulo
  `p^2` on an infinite set of primes, corrections divisible by `p^2` on squarefree `m > 1`), no
  member meets `TargetD p 1 1`.
* `mod9_iff`: `a_1 B_1 + a_2 B_2 + a_3 B_3` (built as `fam {1, 2, 3} a zpowZeta hcorr`) meets
  `TargetD 3 1 1` if and only if `9 ∣ a_1`, `9 ∣ a_2` and `3 ∤ a_3`.
* `d3_ternary`: `D_3(x) = ⌊x^(1/3)⌋ + 3 H(x)` for every natural `x`.
* `piMod3_correct`: `piMod3 x = π(x) mod 3` for every natural `x`.
-/

open Finset ArithmeticFunction
open scoped Nat ArithmeticFunction.omega ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace M2Polymath

/-! ## Kempner values, Dirichlet powers, the family and the targets -/

/-- The Kempner value `S(p^k)`: the least `N` such that `p^k` divides `N!`. -/
noncomputable def kempner (p k : ℕ) : ℕ := sInf {N : ℕ | p ^ k ∣ N !}

/-- The core of signed degree `z`: the Dirichlet power `ζ^z` for `z ≥ 0` and `μ^|z|` for `z < 0`. -/
noncomputable def zpowZeta (z : ℤ) : ArithmeticFunction ℤ :=
  if 0 ≤ z then (ζ : ArithmeticFunction ℤ) ^ z.toNat else (μ : ArithmeticFunction ℤ) ^ z.natAbs

/-- The family member `∑_{z ∈ T} c_z (G_z * h_z)` (Dirichlet convolution inside). -/
def fam (T : Finset ℤ) (c : ℤ → ℤ) (G h : ℤ → ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => ∑ z ∈ T, c z * (G z * h z) n,
    Finset.sum_eq_zero fun z _ => by rw [ArithmeticFunction.map_zero, mul_zero]⟩

/-- The family member `∑_{i ∈ I} c_i (G_i * h_i)` over an arbitrary finite index set. -/
def famI {ι : Type*} (I : Finset ι) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) :
    ArithmeticFunction ℤ :=
  ⟨fun n => ∑ i ∈ I, c i * (G i * h i) n,
    Finset.sum_eq_zero fun i _ => by rw [ArithmeticFunction.map_zero, mul_zero]⟩

/-- Target `D_k` with offset `v`: at every prime `q`, `f q = p^v u_q` modulo `p^(v+k)` with `p` not
dividing `u_q`; and `f n = 0` modulo `p^(v+k)` whenever `ω(n) ≥ 2`. (The value at `1` and at
higher prime powers is free.) -/
def TargetD (p v k : ℕ) (f : ArithmeticFunction ℤ) : Prop :=
  (∀ q : ℕ, q.Prime → ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ (p : ℤ) ^ (v + k) ∣ f q - p ^ v * u) ∧
    ∀ n : ℕ, 2 ≤ ω n → (p : ℤ) ^ (v + k) ∣ f n

/-- The cheap node set `{1, ..., Z}`. -/
noncomputable def cheapNodes (Z : ℕ) : Finset ℤ := Icc 1 (Z : ℤ)

/-- The signed node set `{-Z, ..., -1} ∪ {1, ..., Z}`. -/
noncomputable def signedNodes (Z : ℕ) : Finset ℤ := Icc (-(Z : ℤ)) (-1) ∪ Icc 1 (Z : ℤ)

/-- Some member of the family with cheap nodes (cores `ζ^z`, `z ∈ {1, ..., Z}`) and corrections
vanishing on squarefree `m > 1` meets `TargetD p v k` for some `v`. -/
def CheapAchievable (p k Z : ℕ) : Prop :=
  ∃ T ⊆ cheapNodes Z, ∃ c : ℤ → ℤ, ∃ h : ℤ → ArithmeticFunction ℤ,
    (∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0) ∧ ∃ v, TargetD p v k (fam T c zpowZeta h)

/-- Some member of the family with signed nodes (cores `ζ^z` and `μ^|z|`,
`z ∈ {-Z, ..., -1} ∪ {1, ..., Z}`) and corrections vanishing on squarefree `m > 1` meets
`TargetD p v k` for some `v`. -/
def SignedAchievable (p k Z : ℕ) : Prop :=
  ∃ T ⊆ signedNodes Z, ∃ c : ℤ → ℤ, ∃ h : ℤ → ArithmeticFunction ℤ,
    (∀ z ∈ T, ∀ m, Squarefree m → 1 < m → h z m = 0) ∧ ∃ v, TargetD p v k (fam T c zpowZeta h)

/-- Target U modulo `p^k`: the prime indicator modulo `p^k` on primes and on squarefree `n` with
`ω(n) ≥ 2` (the values at `1` and at non-squarefree `n` are free). -/
def TargetU (p k : ℕ) (f : ArithmeticFunction ℤ) : Prop :=
  (∀ q : ℕ, q.Prime → (p : ℤ) ^ k ∣ f q - 1) ∧
    ∀ n : ℕ, Squarefree n → 2 ≤ ω n → (p : ℤ) ^ k ∣ f n

/-- `B_z(n) = z^ω(n)` for `n ≥ 1`. -/
def Bz (z : ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else z ^ ω n, rfl⟩

/-- The Dirichlet inverse of `zpowZeta z`: `μ^z` for `z ≥ 0` and `ζ^|z|` for `z < 0`. -/
noncomputable def zinv (z : ℤ) : ArithmeticFunction ℤ :=
  if 0 ≤ z then (μ : ArithmeticFunction ℤ) ^ z.toNat else (ζ : ArithmeticFunction ℤ) ^ z.natAbs

/-- The explicit correction `h_z = (zpowZeta z)⁻¹ * B_z` (integer valued). -/
noncomputable def hcorr (z : ℤ) : ArithmeticFunction ℤ := zinv z * Bz z

/-! ## The ternary divisor sum -/

/-- The integer cube root `⌊x^(1/3)⌋`: the largest `m ≤ x` with `m^3 ≤ x`. -/
def icbrt (x : ℕ) : ℕ := Nat.findGreatest (fun m => m ^ 3 ≤ x) x

/-- The ternary divisor function `d_3 = ζ * ζ * ζ`. -/
def d3 : ArithmeticFunction ℕ := ζ * ζ * ζ

/-- `D_3(x) = ∑_{1 ≤ n ≤ x} d_3(n)`. -/
def D3 (x : ℕ) : ℕ := ∑ n ∈ Ioc 0 x, d3 n

/-- `H(x)`: the number of positive triples `(a, b, c)` with `a b c ≤ x`, `a ≤ b` and `a < c`. -/
def H (x : ℕ) : ℕ :=
  ((Ioc 0 x ×ˢ Ioc 0 x ×ˢ Ioc 0 x).filter
    (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ≤ x ∧ t.1 ≤ t.2.1 ∧ t.1 < t.2.2)).card

/-! ## The certified algorithm for `π(x) mod 3` -/

/-- `bfirst p lo hi`: binary search on `[lo, hi]`; for `p` monotone on `[lo, hi]` it returns the least
`i` in `[lo, hi]` with `p i`, or `hi` if there is none. `bfirstAux` is the search with fuel. -/
def bfirstAux (p : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | n + 1, lo, hi =>
    if lo < hi then
      if p ((lo + hi) / 2) then bfirstAux p n lo ((lo + hi) / 2)
      else bfirstAux p n ((lo + hi) / 2 + 1) hi
    else lo

/-- `bfirst p lo hi`, by structural recursion on the fuel `hi - lo` (enough: each step shrinks
`hi - lo`). -/
def bfirst (p : ℕ → Bool) (lo hi : ℕ) : ℕ := bfirstAux p (hi - lo) lo hi

/-- Integer cube root by bisection. -/
def icbrtF (n : ℕ) : ℕ := bfirst (fun m => decide (n < m ^ 3)) 0 (n + 1) - 1

/-- `#{l < k : P l ≤ y}` for `P` with nonincreasing differences: the argmax `ls` by bisection on the
difference, then the two ends of the superlevel set `{P > y}` by bisection (PROOF_D3_5_9.md, Lemma 6). -/
def countLe (P : ℕ → ℤ) (y : ℤ) (k : ℕ) : ℕ :=
  if k = 0 then 0 else
  let ls := bfirst (fun l => decide (P (l + 1) - P l ≤ 0)) 0 (k - 1)
  if P ls ≤ y then k else
  let left := bfirst (fun l => decide (y < P l)) 0 ls
  let right := bfirst (fun l => decide (l = k ∨ P l ≤ y)) ls k
  k - (right - left)

/-- Last continued-fraction convergent `p/q` of `u/v` with `q ≤ Q` (Euclid, with fuel). -/
def approxAux (Q : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, _, _, _, _, _, _, best => best
  | fuel + 1, u, v, p0, q0, p1, q1, best =>
    if v = 0 then best else
    if Q < u / v * q1 + q0 then best
    else approxAux Q fuel v (u % v) p1 q1 (u / v * p1 + p0) (u / v * q1 + q0)
      (u / v * p1 + p0, u / v * q1 + q0)

/-- `(a, q)`: the last convergent of `u / v` with denominator at most `Q` (PROOF_D3_5_9.md, Lemma 2). -/
def approx (u v Q : ℕ) : ℕ × ℕ := approxAux Q (2 * Nat.log2 v + 8) u v 0 1 1 0 (0, 0)

/-- Direct columns: `∑_{n0 ≤ b < n0 + len} floor(y / b)`. -/
def direct (y n0 len : ℕ) : ℤ := ∑ b ∈ Ico n0 (n0 + len), ((y / b : ℕ) : ℤ)

/-- The three level counts of one residue class (PROOF_D3_5_9.md, Lemma 5): `∑_{T = f}^{f+2} #{l < k : (T - a l)(m + q l) ≤ y}`. -/
def cnt3 (y a q m f : ℤ) (k : ℕ) : ℤ :=
  (countLe (fun l => (f - a * l) * (m + q * l)) y k : ℤ)
    + (countLe (fun l => (f + 1 - a * l) * (m + q * l)) y k : ℤ)
    + (countLe (fun l => (f + 2 - a * l) * (m + q * l)) y k : ℤ)

/-- The class `ρ = a⁻¹ (s - j) mod q` of the offsets `t` with `(s - a t) mod q = j`. -/
def clsRho (ainv s q j : ℤ) : ℕ := ((ainv * (s - j)) % q).toNat

/-- The correction of class `ρ`: counts minus `k`. -/
def corr (y n0 a q s : ℤ) (k ρ : ℕ) : ℤ := cnt3 y a q (n0 + ρ) ((s - a * ρ) / q) k - k

/-- The fast block sum over `n0 ≤ n < n0 + k q`: linear part (PROOF_D3_5_9.md, Lemma 4) plus the corrections of the
classes `j ∈ J = {0, q - 2, q - 1} (mod q)` (PROOF_D3_5_9.md, Lemmas 3', 5, 6). -/
def blockFast (y n0 a q ainv : ℤ) (k : ℕ) : ℤ :=
  (2 * k * (q * y / n0) - k * (a + 1) * (q - 1) - a * q * k * (k - 1)) / 2
    + ∑ j ∈ ({0, (q - 2) % q, (q - 1) % q} : Finset ℤ),
        corr y n0 a q (q * y / n0) k (clsRho ainv (q * y / n0) q j)

/-- One block starting at `n0 ≤ r`: returns its length `H ≥ 1` and its sum. The hypotheses of the
window lemma are checked at run time (they hold by PROOF_D3_5_9.md, Lemmas 2 and 3); if a check fails the block
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

/-- `B(x)` with the inner sums by the block routine. -/
def BsumF (x : ℕ) : ℤ :=
  ∑ a ∈ Icc 1 (icbrtF x), ((blockS (x / a) (a - 1) : ℤ)
    - (((Nat.sqrt (x / a) : ℤ) * ((Nat.sqrt (x / a) : ℤ) - 1) - ((a : ℤ) - 1) * ((a : ℤ) - 2)) / 2))

/-- The correction term `E_ab(x)` of the ternary count. -/
def EabF (x : ℕ) : ℤ := ∑ a ∈ Icc 1 (icbrtF x), (((x / a ^ 2 : ℕ) : ℤ) - a + 1)

/-- The correction term `E_bc(x)` of the ternary count. -/
def EbcF (x : ℕ) : ℤ := ∑ a ∈ Icc 1 (icbrtF x), ((Nat.sqrt (x / a) : ℤ) - a + 1)

/-- `D_3(x) = 6 B - 3 E_ab - 3 E_bc + m`, computed with the block routine. -/
def D3fastZ (x : ℕ) : ℤ := 6 * BsumF x - 3 * EabF x - 3 * EbcF x + icbrtF x

/-- **The fast algorithm** for `D_3(x)`. -/
def D3fast (x : ℕ) : ℕ := (D3fastZ x).toNat

/-- The integer `k`-th root: the largest `m ≤ x` with `m^k ≤ x`. -/
def iroot (k x : ℕ) : ℕ := Nat.findGreatest (fun m => m ^ k ≤ x) x

/-- `H(y) mod 3` read off a `D_3 mod 9` oracle `o`. -/
def HofD (o : ℕ → ℕ) (y : ℕ) : ZMod 3 := (((o y + 9 - icbrt y % 9) % 9 / 3 : ℕ) : ZMod 3)

/-- `G(y) mod 3` from an `H mod 3` oracle `h`: `∑_{c ≤ y^(1/3)} μ(c) h(⌊y / c^3⌋)`. -/
def GofH (h : ℕ → ZMod 3) (y : ℕ) : ZMod 3 :=
  ∑ c ∈ Icc 1 (icbrt y), ((μ c : ℤ) : ZMod 3) * h (y / c ^ 3)

/-- `π(x) mod 3` from a `G mod 3` oracle `g`: `∑_{j ≤ log_2 x} μ(j) j g(⌊x^(1/j)⌋)`. -/
def piOfG (g : ℕ → ZMod 3) (x : ℕ) : ZMod 3 :=
  ∑ j ∈ Icc 1 (Nat.log 2 x), ((μ j : ℤ) : ZMod 3) * (j : ZMod 3) * g (iroot j x)

/-- The forward reduction: `π(x) mod 3` computed from a `D_3 mod 9` oracle. -/
def piMod3OfD3 (o : ℕ → ℕ) (x : ℕ) : ZMod 3 := piOfG (GofH (HofD o)) x

/-- `π(x) mod 3` from the fast values of `D_3 mod 9`. -/
def piMod3 (x : ℕ) : ZMod 3 := piMod3OfD3 (fun y => D3fast y % 9) x

/-! ## Results -/

/-- **Exact degree, cheap nodes.** For a prime `p` and `k ≥ 1`, the least `Z` such that the family
with cores `ζ^z`, `z ∈ {1, ..., Z}`, reaches target `D_k` is the Kempner value `S(p^k)`. -/
theorem exact_degree_cheap (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | CheapAchievable p k Z} (kempner p k) := by
  sorry

/-- **Exact degree, signed nodes.** For a prime `p` and `k ≥ 1`, the least `Z` such that the family
with cores `ζ^z` and `μ^|z|`, `z ∈ {-Z, ..., -1} ∪ {1, ..., Z}`, reaches target `D_k` is the
Kempner value `S(p^⌈k/2⌉)`. -/
theorem exact_degree_signed (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {Z | SignedAchievable p k Z} (kempner p ((k + 1) / 2)) := by
  sorry

/-- **No prime detection (Corollary A1).** Let `k ≥ 1`. Take multiplicative cores `G_i` whose value
at every prime is the integer `deg i`, corrections `h_i` vanishing on squarefree `m > 1`, and any
integer coefficients. Then no member `∑ c_i (G_i * h_i)` is the prime indicator modulo `p^k`. -/
theorem no_prime_detection (p : ℕ) [Fact p.Prime] {ι : Type*} {k : ℕ} (hk : 1 ≤ k)
    (I : Finset ι) (deg : ι → ℤ) (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative) (hGq : ∀ i ∈ I, ∀ q, q.Prime → G i q = deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → h i m = 0) :
    ¬ TargetU p k (famI I c G h) := by
  sorry

/-- **Degree `p` is needed.** With degrees in `{0, ..., p - 1}`, cores congruent to their degree
modulo `p^2` at every prime of an infinite set `P`, and corrections divisible by `p^2` on squarefree
`m > 1`, no member of the family meets target `D_1` with offset `1`. -/
theorem degree_p_needed (p : ℕ) [Fact p.Prime] {ι : Type*} (I : Finset ι) (deg : ι → ℤ)
    (c : ι → ℤ) (G h : ι → ArithmeticFunction ℤ) (P : Set ℕ) (hP : P.Infinite)
    (hPp : ∀ q ∈ P, q.Prime) (hd : ∀ i ∈ I, 0 ≤ deg i ∧ deg i ≤ p - 1)
    (hG : ∀ i ∈ I, (G i).IsMultiplicative)
    (hGq : ∀ i ∈ I, ∀ q ∈ P, (p : ℤ) ^ 2 ∣ G i q - deg i)
    (hh : ∀ i ∈ I, ∀ m, Squarefree m → 1 < m → (p : ℤ) ^ 2 ∣ h i m) :
    ¬ TargetD p 1 1 (famI I c G h) := by
  sorry

/-- **Modulo 9.** The member `a_1 B_1 + a_2 B_2 + a_3 B_3`, built as `fam {1, 2, 3} a zpowZeta hcorr`,
meets target `D_1` with offset `1` at `p = 3` if and only if `9 ∣ a_1`, `9 ∣ a_2` and `3 ∤ a_3`. -/
theorem mod9_iff (a : ℤ → ℤ) :
    TargetD 3 1 1 (fam {1, 2, 3} a zpowZeta hcorr) ↔
      (9 : ℤ) ∣ a 1 ∧ (9 : ℤ) ∣ a 2 ∧ ¬ (3 : ℤ) ∣ a 3 := by
  sorry

/-- **The ternary identity (M1).** For every natural `x`, `D_3(x) = ⌊x^(1/3)⌋ + 3 H(x)`. -/
theorem d3_ternary (x : ℕ) : D3 x = icbrt x + 3 * H x := by
  sorry

/-- **`π(x) mod 3` is computed correctly.** For every natural `x`, `piMod3 x = π(x) mod 3`. -/
theorem piMod3_correct (x : ℕ) : piMod3 x = (Nat.primeCounting x : ZMod 3) := by
  sorry

end M2Polymath
