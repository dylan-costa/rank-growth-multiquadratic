import Mathlib

/-!
# Constructing the twisting parameters: Lemma `findgoodvaluelemma` and Remark `rem-factoringfree`

Costa, Lozano-Robledo, *Rank growth in quadratic extensions using twists*, Section 5.

Let `f(x) = x³ + A x + B` and `x₀ = x₁ / M²` with `M = qN`. Then
`f(x₀) = F / M⁶` with `F = x₁³ + M⁴ A x₁ + M⁶ B ∈ ℤ` (`f_eval_eq`), so the square-free part `d₀`
of `f(x₀)` is the square-free part of `F`, and `F = d₀ m²` with `m` prime to every `p ∤ F`
(`legendreSym_mul_sq`). We prove:

* `F ≡ x₁³ (mod p)` for every `p ∣ M`, hence `(F / p) = (x₁ / p)` (`legendreSym_F`);
* `F ≡ 1 (mod 8)` if `2 ∣ M` and `x₁ ≡ 1 (mod 8)` (`F_modEq_one_eight`);
* `F` has the sign of `x₁` when `|x₁| ≥ (|A| + |B| + 1) M²` (`F_pos`, `F_neg`);
* the factoring-free criterion: if `(F_k / q_k) = -1` and `(F_k / q_j) = 1` for `j < k`, no
  product `∏_{k ∈ S} F_k`, `S ≠ ∅`, is a square (`prod_not_isSquare`).

That the last property is equivalent to `[ℚ(√d₁, …, √dₙ) : ℚ] = 2ⁿ` is classical Kummer theory and
is not formalized here.
-/

namespace RankGrowth

open Finset

/-- `F = x₁³ + M⁴ A x₁ + M⁶ B`, the numerator of `f(x₁ / M²) = F / M⁶`. -/
def numF (A B x₁ M : ℤ) : ℤ := x₁ ^ 3 + M ^ 4 * A * x₁ + M ^ 6 * B

/-- `f(x₁ / M²) = F / M⁶`. -/
theorem f_eval_eq (A B x₁ M : ℤ) (hM : M ≠ 0) :
    ((x₁ : ℚ) / M ^ 2) ^ 3 + A * ((x₁ : ℚ) / M ^ 2) + B = (numF A B x₁ M : ℚ) / (M : ℚ) ^ 6 := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  unfold numF
  push_cast
  field_simp

/-- `F ≡ x₁³ (mod p)` for every `p ∣ M`. -/
theorem numF_modEq (A B x₁ M p : ℤ) (hp : p ∣ M) : numF A B x₁ M ≡ x₁ ^ 3 [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  have : x₁ ^ 3 - numF A B x₁ M = M * (-(M ^ 3 * A * x₁ + M ^ 5 * B)) := by
    unfold numF
    ring
  rw [this]
  exact Dvd.dvd.mul_right hp _

/-- `(F / p) = (s / p)` when `p ∣ M`, `x₁ ≡ s (mod p)` and `p ∤ s`. -/
theorem legendreSym_F (p : ℕ) [Fact p.Prime] (A B x₁ M s : ℤ) (hpM : (p : ℤ) ∣ M)
    (hx : x₁ ≡ s [ZMOD p]) (hs : (s : ZMod p) ≠ 0) :
    legendreSym p (numF A B x₁ M) = legendreSym p s := by
  have hxs : (x₁ : ZMod p) = (s : ZMod p) := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hx
  have h1 : legendreSym p (numF A B x₁ M) = legendreSym p (x₁ ^ 3) := by
    rw [legendreSym.mod p (numF A B x₁ M), legendreSym.mod p (x₁ ^ 3)]
    rw [show numF A B x₁ M % p = x₁ ^ 3 % p from numF_modEq A B x₁ M p hpM]
  have h2 : legendreSym p (x₁ ^ 3) = legendreSym p x₁ := by
    rw [show x₁ ^ 3 = x₁ * x₁ ^ 2 by ring, legendreSym.mul, legendreSym.sq_one' p (by rw [hxs]; exact hs),
      mul_one]
  have h3 : legendreSym p x₁ = legendreSym p s := by
    rw [legendreSym.mod p x₁, legendreSym.mod p s, show x₁ % p = s % p from hx]
  rw [h1, h2, h3]

/-- If `s` is a nonzero square mod `p`, then `(F / p) = 1` (the primes `p_i` dividing `N`). -/
theorem legendreSym_F_eq_one (p : ℕ) [Fact p.Prime] (A B x₁ M s : ℤ) (hpM : (p : ℤ) ∣ M)
    (hx : x₁ ≡ s [ZMOD p]) (hs : (s : ZMod p) ≠ 0) (hsq : IsSquare (s : ZMod p)) :
    legendreSym p (numF A B x₁ M) = 1 := by
  rw [legendreSym_F p A B x₁ M s hpM hx hs]
  exact (legendreSym.eq_one_iff p hs).mpr hsq

/-- If `t` is a non-square mod `p`, then `(F / p) = -1` (the primes `q_j`). -/
theorem legendreSym_F_eq_neg_one (p : ℕ) [Fact p.Prime] (A B x₁ M t : ℤ) (hpM : (p : ℤ) ∣ M)
    (hx : x₁ ≡ t [ZMOD p]) (ht : (t : ZMod p) ≠ 0) (hnsq : ¬ IsSquare (t : ZMod p)) :
    legendreSym p (numF A B x₁ M) = -1 := by
  rw [legendreSym_F p A B x₁ M t hpM hx ht]
  exact (legendreSym.eq_neg_one_iff p).mpr hnsq

/-- The square-free part has the same Legendre symbol: `(d m² / p) = (d / p)` if `p ∤ m`. -/
theorem legendreSym_mul_sq (p : ℕ) [Fact p.Prime] (d m : ℤ) (hm : (m : ZMod p) ≠ 0) :
    legendreSym p (d * m ^ 2) = legendreSym p d := by
  rw [legendreSym.mul, legendreSym.sq_one' p hm, mul_one]

/-- `F ≡ 1 (mod 8)` if `2 ∣ M` and `x₁ ≡ 1 (mod 8)`. -/
theorem numF_modEq_one_eight (A B x₁ M : ℤ) (hM : 2 ∣ M) (hx : x₁ ≡ 1 [ZMOD 8]) :
    numF A B x₁ M ≡ 1 [ZMOD 8] := by
  obtain ⟨m, rfl⟩ := hM
  have h1 : numF A B x₁ (2 * m) ≡ x₁ ^ 3 [ZMOD 8] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-(2 * m ^ 4 * A * x₁ + 8 * m ^ 6 * B), by unfold numF; ring⟩
  have h2 : x₁ ^ 3 ≡ 1 ^ 3 [ZMOD 8] := hx.pow 3
  rw [one_pow] at h2
  exact h1.trans h2

/-- **Sign of `d₀`.** If `x₁ ≥ (|A| + |B| + 1) M²` and `M ≠ 0`, then `F > 0`. -/
theorem numF_pos (A B x₁ M : ℤ) (hM : M ≠ 0) (hx : (|A| + |B| + 1) * M ^ 2 ≤ x₁) :
    0 < numF A B x₁ M := by
  unfold numF
  set m := M ^ 2 with hm
  have hm0 : 0 < m := by positivity
  have hA := abs_nonneg A
  have hB := abs_nonneg B
  have hxm : m ≤ x₁ := by nlinarith
  have hx0 : 0 < x₁ := lt_of_lt_of_le hm0 hxm
  have h4 : M ^ 4 = m * m := by rw [hm]; ring
  have h6 : M ^ 6 = m * m * m := by rw [hm]; ring
  rw [h4, h6]
  -- `x₁³ ≥ x₁ · ((|A|+|B|+1) m)² ≥ x₁ m² (|A| + |B| + 1)`
  have hK : (1 : ℤ) ≤ |A| + |B| + 1 := by linarith
  have hsq : ((|A| + |B| + 1) * m) ^ 2 ≤ x₁ ^ 2 := by
    have : 0 ≤ (|A| + |B| + 1) * m := by positivity
    nlinarith
  have hcube : x₁ * (m * m) * (|A| + |B| + 1) ≤ x₁ ^ 3 := by
    have h' : (m * m) * (|A| + |B| + 1) ≤ ((|A| + |B| + 1) * m) ^ 2 := by nlinarith
    nlinarith
  have hAx : -(m * m * |A| * x₁) ≤ m * m * A * x₁ := by
    have := neg_abs_le A
    have hp : 0 ≤ m * m * x₁ := by positivity
    nlinarith
  have hBx : -(m * m * m * |B|) ≤ m * m * m * B := by
    have := neg_abs_le B
    have hp : 0 ≤ m * m * m := by positivity
    nlinarith
  have hmB : m * m * m * |B| ≤ m * m * x₁ * |B| := by
    have hp : 0 ≤ m * m * |B| := by positivity
    nlinarith
  have hpos : 0 < m * m * x₁ := by positivity
  nlinarith

/-- `F < 0` if `x₁ ≤ -(|A| + |B| + 1) M²` and `M ≠ 0`. -/
theorem numF_neg (A B x₁ M : ℤ) (hM : M ≠ 0) (hx : x₁ ≤ -((|A| + |B| + 1) * M ^ 2)) :
    numF A B x₁ M < 0 := by
  have h := numF_pos A (-B) (-x₁) M hM (by rw [abs_neg]; linarith)
  have : numF A (-B) (-x₁) M = -numF A B x₁ M := by unfold numF; ring
  linarith

/-- **The factoring-free criterion (Remark `rem-factoringfree`).** Let `q₀, …, q_{n-1}` be primes and
`F₀, …, F_{n-1}` integers with `(F_k / q_k) = -1` and `(F_k / q_j) = 1` for `j < k`. Then no product
`∏_{k ∈ S} F_k` with `S ≠ ∅` is a square: its Legendre symbol at `q_s`, `s = min S`, is `-1`. -/
theorem prod_not_isSquare {n : ℕ} (q : Fin n → ℕ) [∀ k, Fact (q k).Prime] (F : Fin n → ℤ)
    (hdiag : ∀ k, legendreSym (q k) (F k) = -1)
    (hlow : ∀ j k, j < k → legendreSym (q j) (F k) = 1)
    (S : Finset (Fin n)) (hS : S.Nonempty) : ¬ IsSquare (∏ k ∈ S, F k) := by
  set s := S.min' hS with hsdef
  have hsS : s ∈ S := S.min'_mem hS
  have hmul : ∀ U : Finset (Fin n),
      legendreSym (q s) (∏ k ∈ U, F k) = ∏ k ∈ U, legendreSym (q s) (F k) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp [legendreSym.at_one]
    | insert a U ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, legendreSym.mul, ih]
  have hleg : legendreSym (q s) (∏ k ∈ S, F k) = -1 := by
    rw [hmul S, ← Finset.mul_prod_erase S _ hsS, hdiag s]
    rw [Finset.prod_eq_one]
    · ring
    · intro k hk
      have hkS : k ∈ S := Finset.mem_of_mem_erase hk
      have hks : k ≠ s := Finset.ne_of_mem_erase hk
      have hle : s ≤ k := S.min'_le k hkS
      exact hlow s k (lt_of_le_of_ne hle (Ne.symm hks))
  rintro ⟨r, hr⟩
  rw [hr, legendreSym.mul] at hleg
  nlinarith [mul_self_nonneg (legendreSym (q s) r)]

/-! ### Lemma 5.4 for the square-free part `d₀`

Write `F = d₀ m²` with `d₀` the square-free part of `f(x₀)` (up to the square `M⁶`). The statements
below only use `F = d₀ m²`, not square-freeness. -/

/-- An integer with Legendre symbol `-1` at some prime is not a square. -/
theorem not_isSquare_of_legendreSym_eq_neg_one (p : ℕ) [Fact p.Prime] (a : ℤ)
    (h : legendreSym p a = -1) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  rw [legendreSym.mul] at h
  nlinarith [mul_self_nonneg (legendreSym p r)]

/-- If `p ∤ F` and `F = d₀ m²`, then `p ∤ m` and `(d₀ / p) = (F / p)`. -/
theorem legendreSym_d0 (p : ℕ) [Fact p.Prime] (F d₀ m : ℤ) (hF : F = d₀ * m ^ 2)
    (hp : (F : ZMod p) ≠ 0) : legendreSym p d₀ = legendreSym p F := by
  have hm : (m : ZMod p) ≠ 0 := by
    intro h0
    apply hp
    rw [hF]
    push_cast
    rw [h0]
    ring
  rw [hF, legendreSym_mul_sq p d₀ m hm]

/-- `(F / p) ≠ 0`, i.e. `p ∤ F`, when `p ∣ M` and `x₁ ≡ s (mod p)` with `p ∤ s`. -/
theorem numF_ne_zero_mod (p : ℕ) [Fact p.Prime] (A B x₁ M s : ℤ) (hpM : (p : ℤ) ∣ M)
    (hx : x₁ ≡ s [ZMOD p]) (hs : (s : ZMod p) ≠ 0) : ((numF A B x₁ M : ℤ) : ZMod p) ≠ 0 := by
  have h1 : ((numF A B x₁ M : ℤ) : ZMod p) = ((x₁ ^ 3 : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (numF_modEq A B x₁ M p hpM)
  have hxs : (x₁ : ZMod p) = (s : ZMod p) := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hx
  rw [h1]
  push_cast
  rw [hxs]
  exact pow_ne_zero 3 hs

/-- **Lemma 5.4, at the primes `pᵢ`.** `(d₀ / pᵢ) = 1`. -/
theorem legendreSym_d0_eq_one (p : ℕ) [Fact p.Prime] (A B x₁ M s d₀ m : ℤ) (hpM : (p : ℤ) ∣ M)
    (hx : x₁ ≡ s [ZMOD p]) (hs : (s : ZMod p) ≠ 0) (hsq : IsSquare (s : ZMod p))
    (hF : numF A B x₁ M = d₀ * m ^ 2) : legendreSym p d₀ = 1 := by
  rw [legendreSym_d0 p _ d₀ m hF (numF_ne_zero_mod p A B x₁ M s hpM hx hs)]
  exact legendreSym_F_eq_one p A B x₁ M s hpM hx hs hsq

/-- **Lemma 5.4, at the primes `q_j`.** `(d₀ / q_j) = -1`; in particular `d₀` is not a square. -/
theorem legendreSym_d0_eq_neg_one (p : ℕ) [Fact p.Prime] (A B x₁ M t d₀ m : ℤ)
    (hpM : (p : ℤ) ∣ M) (hx : x₁ ≡ t [ZMOD p]) (ht : (t : ZMod p) ≠ 0)
    (hnsq : ¬ IsSquare (t : ZMod p)) (hF : numF A B x₁ M = d₀ * m ^ 2) :
    legendreSym p d₀ = -1 ∧ ¬ IsSquare d₀ := by
  have h : legendreSym p d₀ = -1 := by
    rw [legendreSym_d0 p _ d₀ m hF (numF_ne_zero_mod p A B x₁ M t hpM hx ht)]
    exact legendreSym_F_eq_neg_one p A B x₁ M t hpM hx ht hnsq
  exact ⟨h, not_isSquare_of_legendreSym_eq_neg_one p d₀ h⟩

/-- If `d m² ≡ 1 (mod 8)` then `d ≡ 1 (mod 8)` (`m` is odd, so `m² ≡ 1`). -/
theorem modEq_one_eight_of_mul_sq (d m : ℤ) (h : d * m ^ 2 ≡ 1 [ZMOD 8]) : d ≡ 1 [ZMOD 8] := by
  have h' : ((d * m ^ 2 : ℤ) : ZMod 8) = ((1 : ℤ) : ZMod 8) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
  push_cast at h'
  have key : ∀ a b : ZMod 8, a * b ^ 2 = 1 → a = 1 := by decide
  have := key _ _ h'
  exact (ZMod.intCast_eq_intCast_iff _ _ 8).mp (by push_cast; exact this)

/-- **Lemma 5.4, `d₀ ≡ 1 (mod 8)`** if `2 ∣ M` and `x₁ ≡ 1 (mod 8)`. -/
theorem d0_modEq_one_eight (A B x₁ M d₀ m : ℤ) (hM : 2 ∣ M) (hx : x₁ ≡ 1 [ZMOD 8])
    (hF : numF A B x₁ M = d₀ * m ^ 2) : d₀ ≡ 1 [ZMOD 8] :=
  modEq_one_eight_of_mul_sq d₀ m (hF ▸ numF_modEq_one_eight A B x₁ M hM hx)

/-- **Lemma 5.4, the sign of `d₀`.** If `x₁ ≥ (|A| + |B| + 1) M²`, then `d₀ > 0`. -/
theorem d0_pos (A B x₁ M d₀ m : ℤ) (hM : M ≠ 0) (hx : (|A| + |B| + 1) * M ^ 2 ≤ x₁)
    (hF : numF A B x₁ M = d₀ * m ^ 2) : 0 < d₀ := by
  have h := numF_pos A B x₁ M hM hx
  rw [hF] at h
  rcases lt_trichotomy d₀ 0 with hd | hd | hd
  · nlinarith [sq_nonneg m]
  · rw [hd, zero_mul] at h; exact absurd h (lt_irrefl 0)
  · exact hd

/-- **Lemma 5.4, the sign of `d₀`.** If `x₁ ≤ -(|A| + |B| + 1) M²`, then `d₀ < 0`. -/
theorem d0_neg (A B x₁ M d₀ m : ℤ) (hM : M ≠ 0) (hx : x₁ ≤ -((|A| + |B| + 1) * M ^ 2))
    (hF : numF A B x₁ M = d₀ * m ^ 2) : d₀ < 0 := by
  have h := numF_neg A B x₁ M hM hx
  rw [hF] at h
  rcases lt_trichotomy d₀ 0 with hd | hd | hd
  · exact hd
  · rw [hd, zero_mul] at h; exact absurd h (lt_irrefl 0)
  · nlinarith [sq_nonneg m]

/-! ### Remark 5.7: the square-free part of a product has a new prime factor -/

/-- **Remark 5.7 (last part).** Let `d₀, …, d_{n-1}` satisfy the hypotheses of
`prod_not_isSquare`, with every `d_k ≡ 1 (mod 8)` and coprime to `K` (`K = 210 N_E`). Let `S` be
non-empty and `∏_{k ∈ S} d_k = D m²` (`D` the square-free part). Then `D ≡ 1 (mod 8)`, `D` is
coprime to `K`, `D` is not a square, `D ≠ ±1`, and `D` has a prime factor `ℓ ∤ K`. -/
theorem sqfree_part_prod {n : ℕ} (q : Fin n → ℕ) [∀ k, Fact (q k).Prime] (d : Fin n → ℤ) (K : ℤ)
    (hdiag : ∀ k, legendreSym (q k) (d k) = -1)
    (hlow : ∀ j k, j < k → legendreSym (q j) (d k) = 1)
    (h8 : ∀ k, d k ≡ 1 [ZMOD 8]) (hK : ∀ k, IsCoprime (d k) K)
    (S : Finset (Fin n)) (hS : S.Nonempty) (D m : ℤ) (hD : ∏ k ∈ S, d k = D * m ^ 2) :
    D ≡ 1 [ZMOD 8] ∧ IsCoprime D K ∧ ¬ IsSquare D ∧ D ≠ 1 ∧ D ≠ -1 ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : ℤ) ∣ D ∧ ¬ (ℓ : ℤ) ∣ K := by
  have hP8 : ∏ k ∈ S, d k ≡ 1 [ZMOD 8] := by
    have : ∀ U : Finset (Fin n), ∏ k ∈ U, d k ≡ 1 [ZMOD 8] := by
      intro U
      induction U using Finset.induction_on with
      | empty => simp [Int.ModEq.refl]
      | insert a U ha ih =>
        rw [Finset.prod_insert ha]
        simpa using (h8 a).mul ih
    exact this S
  have hPK : IsCoprime (∏ k ∈ S, d k) K := IsCoprime.prod_left fun k _ => hK k
  have hD8 : D ≡ 1 [ZMOD 8] := modEq_one_eight_of_mul_sq D m (hD ▸ hP8)
  have hDK : IsCoprime D K := by
    rw [hD] at hPK
    exact hPK.of_mul_left_left
  have hDsq : ¬ IsSquare D := by
    rintro ⟨r, rfl⟩
    exact prod_not_isSquare q d hdiag hlow S hS ⟨r * m, by rw [hD]; ring⟩
  have hD1 : D ≠ 1 := by
    rintro rfl
    exact hDsq ⟨1, by ring⟩
  have hDm1 : D ≠ -1 := by
    rintro rfl
    have := Int.ModEq.eq hD8
    norm_num at this
  refine ⟨hD8, hDK, hDsq, hD1, hDm1, ?_⟩
  have habs : D.natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.mp h with h | h
    · exact hD1 (by exact_mod_cast h)
    · exact hDm1 (by rw [h]; rfl)
  obtain ⟨ℓ, hℓ, hℓD⟩ := Nat.exists_prime_and_dvd habs
  refine ⟨ℓ, hℓ, Int.natCast_dvd.mpr hℓD, fun hℓK => ?_⟩
  have hdvd1 : (ℓ : ℤ) ∣ 1 := by
    obtain ⟨u, v, huv⟩ := hDK
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hℓD) u) (dvd_mul_of_dvd_right hℓK v)
  have := Int.eq_one_of_dvd_one (by positivity) hdvd1
  exact hℓ.one_lt.ne' (by exact_mod_cast this)

end RankGrowth
