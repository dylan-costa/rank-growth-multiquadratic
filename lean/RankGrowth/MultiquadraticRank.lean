import RankGrowth.RootNumbers

/-!
# Rank of `E` over a multi-quadratic field: Lemma `lem:multiquadratic-rank`

Costa, Lozano-Robledo, *Rank growth in quadratic extensions using twists*, Section 5.

A `TwistFamily n` records, for every subset `S ⊆ {0, …, n-1}`, the rank `R_{E^{d_S}/ℚ}` and the
root number `W(E^{d_S})` of the twist by `d_S = ∏_{k ∈ S} d_k` (`S = ∅` is `E` itself), together
with the hypotheses of the lemma that are not about ranks over `L_n`:

* `rootNumber_sign`: root numbers are `±1`;
* `rootNumber_mul`: Eq. (rootnumber-product), which follows from Dokchitser's formula when the
  discriminants of the `ℚ(√d_k)` are prime to `N_E` (see `RankGrowth.rootNumber_product`);
* `rank_pos`: `R_{E^{d_k}/ℚ} ≥ 1` for every `k`.

By Kida's formula (Proposition `prop-kida`), `R_{E/L_n} = ∑_S R_{E^{d_S}/ℚ}` when
`[L_n : ℚ] = 2ⁿ`; this is `TwistFamily.rankL`. The Parity Conjecture for the twists `E^d`,
`d ≠ 1` (or the finiteness of some `Sha(E^d/ℚ)[p^∞]`, via `RankGrowth.parity_of_pparity`) is the
hypothesis `TwistFamily.Parity`.

The main result is `TwistFamily.two_mul_sum_ge`, a single counting inequality from which every
part of the lemma (and Remark `rem-signpatterns`) follows.
-/

namespace RankGrowth

open Finset

/-- The ranks and root numbers of the `2ⁿ` twists `E^{d_S}`, `S ⊆ {0, …, n-1}`. -/
structure TwistFamily (n : ℕ) where
  /-- `rank S = R_{E^{d_S}/ℚ}`; `rank ∅ = R_{E/ℚ}`. -/
  rank : Finset (Fin n) → ℕ
  /-- `rootNumber S = W(E^{d_S})`; `rootNumber ∅ = W(E)`. -/
  rootNumber : Finset (Fin n) → ℤ
  rootNumber_sign : ∀ S, rootNumber S = 1 ∨ rootNumber S = -1
  /-- Eq. (rootnumber-product). -/
  rootNumber_mul : ∀ S, rootNumber S = rootNumber ∅ ^ (S.card + 1) * ∏ k ∈ S, rootNumber {k}
  rank_pos : ∀ k, 1 ≤ rank {k}

namespace TwistFamily

variable {n : ℕ} (T : TwistFamily n)

/-- `R_{E/L_n} = ∑_{d ∈ 𝒟ₙ} R_{E^d/ℚ}` (Kida's formula, Proposition `prop-kida`). -/
def rankL : ℕ := ∑ S, T.rank S

/-- The Parity Conjecture for every twist `E^d`, `d ∈ 𝒟ₙ`, `d ≠ 1`. -/
def Parity : Prop := ∀ S : Finset (Fin n), S ≠ ∅ → (-1 : ℤ) ^ (T.rank S) = T.rootNumber S

/-- The number `p` of indices `k` with `W(E^{d_k}) = +1`. -/
def numPlus : ℕ := (univ.filter fun k : Fin n => T.rootNumber {k} = 1).card

lemma rankL_eq : T.rankL = T.rank ∅ + ∑ S ∈ univ.erase ∅, T.rank S :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm

/-! ### Part (1) -/

/-- **Lemma `lem:multiquadratic-rank` (1).** `R_{E/L_n} ≥ R_{E/ℚ} + n`. -/
theorem part1 : T.rank ∅ + n ≤ T.rankL := by
  have hsub : insert ∅ (univ.image fun k : Fin n => ({k} : Finset (Fin n))) ⊆ univ :=
    Finset.subset_univ _
  have hnot : (∅ : Finset (Fin n)) ∉ univ.image fun k : Fin n => ({k} : Finset (Fin n)) := by
    simp
  calc T.rank ∅ + n = T.rank ∅ + ∑ _k : Fin n, 1 := by simp
    _ ≤ T.rank ∅ + ∑ k : Fin n, T.rank {k} := by
        gcongr with k
        exact T.rank_pos k
    _ = ∑ S ∈ insert ∅ (univ.image fun k : Fin n => ({k} : Finset (Fin n))), T.rank S := by
        rw [Finset.sum_insert hnot, Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
    _ ≤ T.rankL := Finset.sum_le_sum_of_subset hsub

/-! ### The counting inequality -/

lemma one_sub_le_two_mul (r : ℕ) (w : ℤ) (hw : w = 1 ∨ w = -1) (hpar : (-1 : ℤ) ^ r = w) :
    1 - w ≤ 2 * (r : ℤ) := by
  rcases hw with rfl | rfl
  · simp
  · have : r ≠ 0 := by
      rintro rfl
      norm_num at hpar
    omega

lemma two_le_of_even_sign (r : ℕ) (hpar : (-1 : ℤ) ^ r = 1) (hr : 1 ≤ r) : 2 ≤ r := by
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨m, rfl⟩ := he
    omega
  · rw [ho.neg_one_pow] at hpar
    norm_num at hpar

/-- **The counting inequality.** Under Parity, every twist `E^d`, `d ≠ 1`, with `W(E^d) = -1` has
odd, hence positive, rank, and every `E^{d_k}` with `W(E^{d_k}) = +1` has even positive rank, hence
rank `≥ 2`. Summing,
`2 ∑_{S ≠ ∅} R_{E^{d_S}} ≥ (2ⁿ - 1) - (∑_S W(E^{d_S}) - W(E)) + 4p`. -/
theorem two_mul_sum_ge (hP : T.Parity) :
    ((2 : ℤ) ^ n - 1) - (∑ S, T.rootNumber S - T.rootNumber ∅) + 4 * (T.numPlus : ℤ)
      ≤ 2 * ∑ S ∈ univ.erase ∅, (T.rank S : ℤ) := by
  set P := univ.filter fun k : Fin n => T.rootNumber {k} = 1 with hPdef
  set I := P.image fun k : Fin n => ({k} : Finset (Fin n)) with hIdef
  -- the bound for each twist
  have hS : ∀ S ∈ univ.erase (∅ : Finset (Fin n)),
      (1 - T.rootNumber S) + (if S ∈ I then 4 else 0) ≤ 2 * (T.rank S : ℤ) := by
    intro S hSmem
    have hne : S ≠ ∅ := Finset.ne_of_mem_erase hSmem
    by_cases hI : S ∈ I
    · obtain ⟨k, hkP, rfl⟩ := Finset.mem_image.mp hI
      have hk1 : T.rootNumber {k} = 1 := (Finset.mem_filter.mp hkP).2
      have h2 := two_le_of_even_sign _ ((hP {k} hne).trans hk1) (T.rank_pos k)
      rw [ite_eq_left hI, hk1]
      omega
    · rw [ite_eq_right hI, add_zero]
      exact one_sub_le_two_mul _ _ (T.rootNumber_sign S) (hP S hne)
  have hsum := Finset.sum_le_sum hS
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  -- the three sums
  have hcard : ((univ.erase (∅ : Finset (Fin n))).card : ℤ) = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    push_cast [this]
    ring
  have hω : ∑ S ∈ univ.erase (∅ : Finset (Fin n)), T.rootNumber S
      = ∑ S, T.rootNumber S - T.rootNumber ∅ :=
    Finset.sum_erase_eq_sub (Finset.mem_univ _)
  have hIsub : I ⊆ univ.erase ∅ := by
    intro S hSI
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hSI
    exact Finset.mem_erase.mpr ⟨Finset.singleton_ne_empty k, Finset.mem_univ _⟩
  have hfour : ∑ S ∈ univ.erase (∅ : Finset (Fin n)), (if S ∈ I then (4 : ℤ) else 0)
      = 4 * (T.numPlus : ℤ) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hIsub, Finset.sum_const, nsmul_eq_mul,
      hIdef, Finset.card_image_of_injective _ Finset.singleton_injective]
    simp only [numPlus, ← hPdef]
    ring
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [hcard, hω, hfour] at hsum
  linarith

/-! ### The four closed forms (Remark `rem-signpatterns`) -/

/-- `∑_S W(E^{d_S})` in terms of `W(E)` and `W(E) W(E^{d_k})`. -/
lemma sum_rootNumber : ∑ S, T.rootNumber S = T.rootNumber ∅ * ∏ k, (1 + T.rootNumber ∅ * T.rootNumber {k}) :=
  sum_rootNumbers T.rootNumber T.rootNumber_mul

lemma numPlus_le : T.numPlus ≤ n := by
  calc T.numPlus ≤ (univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma numPlus_eq_n_iff : T.numPlus = n ↔ ∀ k, T.rootNumber {k} = 1 := by
  unfold numPlus
  constructor
  · intro h k
    have : (univ.filter fun k : Fin n => T.rootNumber {k} = 1) = univ := by
      apply Finset.eq_univ_of_card
      simpa using h
    have hk : k ∈ (univ.filter fun k : Fin n => T.rootNumber {k} = 1) := by
      rw [this]; exact Finset.mem_univ k
    exact (Finset.mem_filter.mp hk).2
  · intro h
    rw [Finset.filter_true_of_mem (fun k _ => h k)]
    simp

lemma numPlus_eq_zero_iff : T.numPlus = 0 ↔ ∀ k, T.rootNumber {k} = -1 := by
  unfold numPlus
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h k
    rcases T.rootNumber_sign {k} with h1 | h1
    · exact absurd h1 (h (Finset.mem_univ k))
    · exact h1
  · intro h k _ h1
    rw [h k] at h1
    norm_num at h1

/-- `W(E) = +1`: the counting bound is `2n` if all `W(E^{d_k}) = +1`, and `2^{n-1} + 2p` otherwise. -/
theorem bound_plus (hP : T.Parity) (h0 : T.rootNumber ∅ = 1) :
    (if T.numPlus = n then 2 * n else 2 ^ (n - 1) + 2 * T.numPlus)
      ≤ ∑ S ∈ univ.erase ∅, T.rank S := by
  have key := T.two_mul_sum_ge hP
  rw [T.sum_rootNumber, h0] at key
  simp only [one_mul] at key
  have hpn := T.numPlus_le
  split_ifs with hp
  · have hall := (T.numPlus_eq_n_iff).mp hp
    rw [prod_one_add_eq_two_pow _ hall, hp] at key
    have : (2 : ℤ) * n ≤ ∑ S ∈ univ.erase ∅, (T.rank S : ℤ) := by linarith
    exact_mod_cast this
  · have hex : ∃ k, T.rootNumber {k} = -1 := by
      by_contra hcon
      push Not at hcon
      exact hp ((T.numPlus_eq_n_iff).mpr fun k =>
        (T.rootNumber_sign {k}).resolve_right (hcon k))
    rw [prod_one_add_eq_zero _ hex] at key
    have hn : 1 ≤ n := by omega
    have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2] at key
    have : ((2 ^ (n - 1) + 2 * T.numPlus : ℕ) : ℤ) ≤ ∑ S ∈ univ.erase ∅, (T.rank S : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- `W(E) = -1`: the counting bound is `2ⁿ - 1` if all `W(E^{d_k}) = -1`, and
`2^{n-1} - 1 + 2p` otherwise. -/
theorem bound_minus (hP : T.Parity) (h0 : T.rootNumber ∅ = -1) :
    (if T.numPlus = 0 then 2 ^ n - 1 else 2 ^ (n - 1) - 1 + 2 * T.numPlus)
      ≤ ∑ S ∈ univ.erase ∅, T.rank S := by
  have key := T.two_mul_sum_ge hP
  rw [T.sum_rootNumber, h0] at key
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  split_ifs with hp
  · have hall := (T.numPlus_eq_zero_iff).mp hp
    have hc : ∀ k, -1 * T.rootNumber {k} = 1 := fun k => by rw [hall k]; norm_num
    rw [prod_one_add_eq_two_pow _ hc, hp] at key
    have : (((2 ^ n - 1 : ℕ)) : ℤ) ≤ ∑ S ∈ univ.erase ∅, (T.rank S : ℤ) := by
      push_cast [hpow]
      linarith
    exact_mod_cast this
  · have hex : ∃ k, -1 * T.rootNumber {k} = -1 := by
      by_contra hcon
      push Not at hcon
      apply hp
      apply (T.numPlus_eq_zero_iff).mpr
      intro k
      rcases T.rootNumber_sign {k} with h1 | h1
      · exact absurd (by rw [h1]; norm_num) (hcon k)
      · exact h1
    rw [prod_one_add_eq_zero _ hex] at key
    have hn : 1 ≤ n := by
      have := T.numPlus_le
      omega
    have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2] at key
    have hpow' : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    have : (((2 ^ (n - 1) - 1 + 2 * T.numPlus : ℕ)) : ℤ) ≤ ∑ S ∈ univ.erase ∅, (T.rank S : ℤ) := by
      push_cast [hpow']
      linarith
    exact_mod_cast this

/-! ### Lemma `lem:multiquadratic-rank`, parts (2)–(4) -/

/-- **Lemma `lem:multiquadratic-rank` (2).** If `W(E) = -1`, `W(E^{d_k}) = +1` for every `k`, and
Parity holds for the twists, then `R_{E/L_n} ≥ R_{E/ℚ} + 2n + 2^{n-1} - 1`. -/
theorem part2 (hP : T.Parity) (hn : 1 ≤ n) (h0 : T.rootNumber ∅ = -1)
    (hk : ∀ k, T.rootNumber {k} = 1) :
    T.rank ∅ + 2 * n + 2 ^ (n - 1) - 1 ≤ T.rankL := by
  have hb := T.bound_minus hP h0
  have hp : T.numPlus = n := (T.numPlus_eq_n_iff).mpr hk
  have hp0 : T.numPlus ≠ 0 := by omega
  rw [ite_eq_right hp0, hp] at hb
  rw [T.rankL_eq]
  have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  omega

/-- **Lemma `lem:multiquadratic-rank` (3), first claim.** If `W(E) = W(E^{d_k}) = -1` for every `k`,
then `W(E^d) = -1` for every `d ∈ 𝒟ₙ`. -/
theorem part3_rootNumber (h0 : T.rootNumber ∅ = -1) (hk : ∀ k, T.rootNumber {k} = -1)
    (S : Finset (Fin n)) : T.rootNumber S = -1 := by
  rw [T.rootNumber_mul S, h0, Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_const, ← pow_add,
    show S.card + 1 + S.card = 2 * S.card + 1 by ring, pow_succ, pow_mul]
  norm_num

/-- **Lemma `lem:multiquadratic-rank` (3)(a).** If every twist `E^d`, `d ≠ 1`, has rank exactly `1`
(as Gross–Zagier and Kolyvagin give when `ord_{s=1} L(E^d, s) = 1`), then
`R_{E/L_n} = R_{E/ℚ} + 2ⁿ - 1`. -/
theorem part3a (hone : ∀ S : Finset (Fin n), S ≠ ∅ → T.rank S = 1) :
    T.rankL = T.rank ∅ + (2 ^ n - 1) := by
  rw [T.rankL_eq, Finset.sum_congr rfl (fun S hS => hone S (Finset.ne_of_mem_erase hS)),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-- **Lemma `lem:multiquadratic-rank` (3)(b).** If `W(E) = W(E^{d_k}) = -1` for every `k` and Parity
holds for the twists (or some `Sha(E^d/ℚ)[p^∞]` is finite for each of them), then
`R_{E/L_n} ≥ R_{E/ℚ} + 2ⁿ - 1`. -/
theorem part3b (hP : T.Parity) (h0 : T.rootNumber ∅ = -1) (hk : ∀ k, T.rootNumber {k} = -1) :
    T.rank ∅ + (2 ^ n - 1) ≤ T.rankL := by
  have hb := T.bound_minus hP h0
  rw [ite_eq_left ((T.numPlus_eq_zero_iff).mpr hk)] at hb
  rw [T.rankL_eq]
  omega

/-- **Lemma `lem:multiquadratic-rank` (3)(b), under BSD.** If every twist `E^d`, `d ≠ 1`, has odd
rank and one of them has rank `≥ 3` (BSD and `ord_{s=1} L(E^{d₀}, s) > 1`), then
`R_{E/L_n} ≥ R_{E/ℚ} + 2ⁿ + 1`. -/
theorem part3b_bsd (hodd : ∀ S : Finset (Fin n), S ≠ ∅ → Odd (T.rank S))
    (S₀ : Finset (Fin n)) (hS₀ : S₀ ≠ ∅) (h3 : 3 ≤ T.rank S₀) :
    T.rank ∅ + 2 ^ n + 1 ≤ T.rankL := by
  have hmem : S₀ ∈ univ.erase (∅ : Finset (Fin n)) :=
    Finset.mem_erase.mpr ⟨hS₀, Finset.mem_univ _⟩
  have hrest : ((univ.erase (∅ : Finset (Fin n))).erase S₀).card ≤
      ∑ S ∈ (univ.erase (∅ : Finset (Fin n))).erase S₀, T.rank S := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro S hS
    have hne : S ≠ ∅ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hS)
    obtain ⟨m, hm⟩ := hodd S hne
    omega
  have hcard : ((univ.erase (∅ : Finset (Fin n))).erase S₀).card = 2 ^ n - 2 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    omega
  rw [T.rankL_eq, ← Finset.add_sum_erase _ _ hmem]
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  -- `2ⁿ ≥ 2` because `S₀ ≠ ∅` forces `n ≥ 1`
  have hn : 1 ≤ n := by
    by_contra h
    push Not at h
    have h0 : n = 0 := by omega
    subst h0
    exact hS₀ (Finset.eq_empty_of_isEmpty S₀)
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- **Lemma `lem:multiquadratic-rank` (4)(a).** If `W(E) = W(E^{d_k}) = +1` for every `k` and Parity
holds for the twists, then `R_{E/L_n} ≥ R_{E/ℚ} + 2n`. -/
theorem part4a (hP : T.Parity) (h0 : T.rootNumber ∅ = 1) (hk : ∀ k, T.rootNumber {k} = 1) :
    T.rank ∅ + 2 * n ≤ T.rankL := by
  have hb := T.bound_plus hP h0
  rw [ite_eq_left ((T.numPlus_eq_n_iff).mpr hk)] at hb
  rw [T.rankL_eq]
  omega

/-- **Lemma `lem:multiquadratic-rank` (4)(b).** If `W(E) = +1`, `W(E^{d_k}) = -1` for every `k`
(`n ≥ 1`) and Parity holds for the twists, then `R_{E/L_n} ≥ R_{E/ℚ} + 2^{n-1}`. -/
theorem part4b (hP : T.Parity) (hn : 1 ≤ n) (h0 : T.rootNumber ∅ = 1)
    (hk : ∀ k, T.rootNumber {k} = -1) :
    T.rank ∅ + 2 ^ (n - 1) ≤ T.rankL := by
  have hb := T.bound_plus hP h0
  have hp : T.numPlus = 0 := (T.numPlus_eq_zero_iff).mpr hk
  rw [ite_eq_right (by omega), hp] at hb
  rw [T.rankL_eq]
  omega

/-- **Lemma `lem:multiquadratic-rank` (4)(c).** If `n ≥ 2`, `W(E) = +1`, `W(E^{d_k}) = +1` for
`k < n - 1` and `W(E^{d_{n-1}}) = -1` (indices start at `0`), and Parity holds for the twists, then
`R_{E/L_n} ≥ R_{E/ℚ} + 2^{n-1} + 2n - 2`. -/
theorem part4c (hP : T.Parity) (hn : 2 ≤ n) (h0 : T.rootNumber ∅ = 1)
    (hk : ∀ k : Fin n, k.val < n - 1 → T.rootNumber {k} = 1)
    (hlast : ∀ k : Fin n, k.val = n - 1 → T.rootNumber {k} = -1) :
    T.rank ∅ + 2 ^ (n - 1) + 2 * n - 2 ≤ T.rankL := by
  have hb := T.bound_plus hP h0
  have hp : T.numPlus = n - 1 := by
    unfold numPlus
    have : (univ.filter fun k : Fin n => T.rootNumber {k} = 1)
        = univ.filter fun k : Fin n => k.val < n - 1 := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h1
        by_contra hlt
        have : k.val = n - 1 := by omega
        rw [hlast k this] at h1
        norm_num at h1
      · exact hk k
    rw [this]
    have hc : (univ.filter fun k : Fin n => k.val < n - 1).card = (Finset.range (n - 1)).card := by
      apply Finset.card_bij (fun k _ => k.val)
      · intro k hk
        simpa using hk
      · intro a _ b _ h
        exact Fin.ext h
      · intro b hb
        have hb' : b < n - 1 := Finset.mem_range.mp hb
        exact ⟨⟨b, by omega⟩, by simpa using hb', rfl⟩
    rw [hc, Finset.card_range]
  rw [ite_eq_right (by omega), hp] at hb
  rw [T.rankL_eq]
  omega

end TwistFamily

end RankGrowth
