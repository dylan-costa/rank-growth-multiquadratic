import Mathlib

/-!
# Root numbers of multi-quadratic twists

Costa, Lozano-Robledo, *Rank growth in quadratic extensions using twists*, Section 4.

Fix square-free integers `d₁, …, dₙ`. The twists `E^d` with `d ∈ 𝒟ₙ` are indexed by subsets
`S ⊆ {0, …, n-1}` (via `d = ∏_{k ∈ S} d_k`); the subset `S = ∅` corresponds to `E` itself.
A root number is a sign `±1`, which we model as an integer.

The input from the literature is Lemma `kronlemma` (V. Dokchitser, Corollary 2): when the
discriminant `D` of `ℚ(√d)` is prime to `N_E`, `W(E^d) = W(E) · (D / -N_E)`, and the Kronecker
symbol `(· / -N_E)` is completely multiplicative in the numerator. We take these two facts as
hypotheses (`hkron`, `hχ`) and derive Eq. (rootnumber-product) and Corollary
`cor-rootnumberoftwistproduct`.
-/

namespace RankGrowth

open Finset

variable {n : ℕ}

lemma mul_self_eq_one_of_sign {x : ℤ} (h : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases h with rfl | rfl <;> norm_num

/-- **Eq. (rootnumber-product).** If `W(E^{d_S}) = W(E) · χ(D_S)` for every `S` (Dokchitser) and
`χ(D_S) = ∏_{k ∈ S} χ(D_k)` (complete multiplicativity of the Kronecker symbol, the square
factors being prime to `N_E`), then `W(E^{d_S}) = W(E)^{|S|+1} ∏_{k ∈ S} W(E^{d_k})`. -/
theorem rootNumber_product (ω χ : Finset (Fin n) → ℤ)
    (hω0 : ω ∅ = 1 ∨ ω ∅ = -1)
    (hkron : ∀ S, ω S = ω ∅ * χ S)
    (hχ : ∀ S, χ S = ∏ k ∈ S, χ {k}) (S : Finset (Fin n)) :
    ω S = ω ∅ ^ (S.card + 1) * ∏ k ∈ S, ω {k} := by
  have h1 : ∀ k, χ {k} = ω ∅ * ω {k} := by
    intro k
    rw [hkron {k}, ← mul_assoc, mul_self_eq_one_of_sign hω0, one_mul]
  rw [hkron S, hχ S, Finset.prod_congr rfl (fun k _ => h1 k), Finset.prod_mul_distrib,
    Finset.prod_const]
  ring

/-- **Corollary `cor-rootnumberoftwistproduct`**, in the form `W(E^D) = W(E)^{n-1} ∏ W(E^{d_k})`
for the full product `D = d₁ ⋯ dₙ` (`n ≥ 1`), using `W(E)² = 1`. -/
theorem rootNumber_full_product (ω : Finset (Fin n) → ℤ) (hω0 : ω ∅ = 1 ∨ ω ∅ = -1)
    (hmul : ∀ S, ω S = ω ∅ ^ (S.card + 1) * ∏ k ∈ S, ω {k}) (hn : 1 ≤ n) :
    ω univ = ω ∅ ^ (n - 1) * ∏ k, ω {k} := by
  rw [hmul univ, Finset.card_univ, Fintype.card_fin]
  have h2 : ω ∅ ^ 2 = 1 := by rw [sq]; exact mul_self_eq_one_of_sign hω0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 + 1 = m + 2 by ring, pow_add, h2, mul_one, Nat.add_sub_cancel]

/-- The root numbers in normalized form: `W(E^{d_S}) = W(E) · ∏_{k ∈ S} (W(E) W(E^{d_k}))`. -/
lemma rootNumber_eq_mul_prod (ω : Finset (Fin n) → ℤ)
    (hmul : ∀ S, ω S = ω ∅ ^ (S.card + 1) * ∏ k ∈ S, ω {k}) (S : Finset (Fin n)) :
    ω S = ω ∅ * ∏ k ∈ S, (ω ∅ * ω {k}) := by
  rw [hmul S, Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- `∑_{S ⊆ {0,…,n-1}} ∏_{k ∈ S} c_k = ∏_k (1 + c_k)`. -/
lemma sum_prod_eq_prod_one_add (c : Fin n → ℤ) :
    ∑ S : Finset (Fin n), ∏ k ∈ S, c k = ∏ k, (1 + c k) := by
  rw [Finset.prod_one_add, Finset.powerset_univ]

/-- The sum of all `2ⁿ` root numbers: `∑_S W(E^{d_S}) = W(E) ∏_k (1 + W(E) W(E^{d_k}))`. -/
lemma sum_rootNumbers (ω : Finset (Fin n) → ℤ)
    (hmul : ∀ S, ω S = ω ∅ ^ (S.card + 1) * ∏ k ∈ S, ω {k}) :
    ∑ S, ω S = ω ∅ * ∏ k, (1 + ω ∅ * ω {k}) := by
  rw [← sum_prod_eq_prod_one_add, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun S _ => rootNumber_eq_mul_prod ω hmul S)

/-- `∏_k (1 + c_k) = 0` as soon as some `c_k = -1`. -/
lemma prod_one_add_eq_zero (c : Fin n → ℤ) (h : ∃ k, c k = -1) : ∏ k, (1 + c k) = 0 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; norm_num)

/-- `∏_k (1 + c_k) = 2ⁿ` if every `c_k = 1`. -/
lemma prod_one_add_eq_two_pow (c : Fin n → ℤ) (h : ∀ k, c k = 1) : ∏ k, (1 + c k) = 2 ^ n := by
  rw [Finset.prod_congr rfl (fun k _ => by rw [h k]), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

/-- The `p`-parity step (Corollary `cor-pparity-sha`): if `s_p = R + corank Sha[p^∞]`,
`(-1)^{s_p} = W` (Monsky, Dokchitser–Dokchitser) and `Sha[p^∞]` is finite (corank `0`), then the
Parity Conjecture `(-1)^R = W` holds for this curve. -/
theorem parity_of_pparity (R s cork : ℕ) (w : ℤ) (hs : s = R + cork) (hpp : (-1 : ℤ) ^ s = w)
    (hfin : cork = 0) : (-1 : ℤ) ^ R = w := by
  rw [← hpp, hs, hfin, add_zero]

end RankGrowth
