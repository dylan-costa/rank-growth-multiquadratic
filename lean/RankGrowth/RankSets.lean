import RankGrowth.SignPatterns

/-!
# The sets `Rk¹_{d,T}` and `Rk^∞_{d,T}`: Remark 1.1, Theorem 1.2 and Remark 5.9

Costa, Lozano-Robledo, *Rank growth in quadratic extensions using twists*.

We model a class of elliptic curves (for instance, all `E/L` with `[L : ℚ] = d` and
`E(L)_tors ≅ T`) as a set `A` in a type `C` of curves, with a `j`-invariant `j : C → J` and a rank
`rk : C → ℕ`. Two curves are geometrically isomorphic iff they have the same `j`-invariant, so
"infinitely many pairwise geometrically non-isomorphic curves" means "infinitely many
`j`-invariants". Then

* `Rk1 A rk = {rk E : E ∈ A}` is `Rk¹_{d,T}`;
* `RkInf A j rk = {R : infinitely many j(E), E ∈ A, rk E ≥ R}` is `Rk^∞_{d,T}`;
* `RkInfExact A j rk` is the variant with rank exactly `R` (Remarks 1.1 and 5.9).

Base change `E ↦ E ×_ℚ L` keeps the `j`-invariant; the facts that it keeps the torsion and gives a
field of degree `2ⁿ` (Theorem 5.6) are encoded in the hypothesis that the base-changed curve lies in
the target class `AL`. Kida's formula and the Parity Conjecture enter through `TwistFamily`.
-/

namespace RankGrowth

open Set

section Sets

variable {C J : Type*}

/-- `Rk¹`: the ranks of the curves in the class `A`. -/
def Rk1 (A : Set C) (rk : C → ℕ) : Set ℕ := rk '' A

/-- `Rk^∞`: the `R` such that infinitely many `j`-invariants occur among the curves of `A` with
rank `≥ R`. -/
def RkInf (A : Set C) (j : C → J) (rk : C → ℕ) : Set ℕ :=
  {R | (j '' {E | E ∈ A ∧ R ≤ rk E}).Infinite}

/-- The exact-rank variant of `Rk^∞` (Remarks 1.1 and 5.9). -/
def RkInfExact (A : Set C) (j : C → J) (rk : C → ℕ) : Set ℕ :=
  {R | (j '' {E | E ∈ A ∧ rk E = R}).Infinite}

variable (A : Set C) (j : C → J) (rk : C → ℕ)

/-- **Remark 1.1.** `Rk^∞` is closed downwards. -/
theorem RkInf_downward {R R' : ℕ} (hR : R ∈ RkInf A j rk) (h : R' ≤ R) :
    R' ∈ RkInf A j rk := by
  refine Set.Infinite.mono ?_ hR
  exact Set.image_mono fun E hE => ⟨hE.1, le_trans h hE.2⟩

theorem RkInfExact_subset : RkInfExact A j rk ⊆ RkInf A j rk := by
  intro R hR
  refine Set.Infinite.mono ?_ hR
  exact Set.image_mono fun E hE => ⟨hE.1, hE.2.ge⟩

/-- **Remark 1.1.** If `S = sup Rk^∞` is finite (the set is non-empty and bounded), then `S` lies in
`Rk^∞`, and infinitely many `j`-invariants occur with rank *exactly* `S`. -/
theorem sSup_mem_RkInfExact (hne : (RkInf A j rk).Nonempty) (hbdd : BddAbove (RkInf A j rk)) :
    sSup (RkInf A j rk) ∈ RkInf A j rk ∧ sSup (RkInf A j rk) ∈ RkInfExact A j rk := by
  set S := sSup (RkInf A j rk) with hS
  have hmem : S ∈ RkInf A j rk := Nat.sSup_mem hne hbdd
  refine ⟨hmem, ?_⟩
  have hnot : S + 1 ∉ RkInf A j rk := fun h => by
    have := le_csSup hbdd h
    omega
  have hfin : (j '' {E | E ∈ A ∧ S + 1 ≤ rk E}).Finite := Set.not_infinite.mp hnot
  have hsplit : j '' {E | E ∈ A ∧ S ≤ rk E}
      ⊆ j '' {E | E ∈ A ∧ rk E = S} ∪ j '' {E | E ∈ A ∧ S + 1 ≤ rk E} := by
    rintro _ ⟨E, ⟨hA, hle⟩, rfl⟩
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact Or.inl ⟨E, ⟨hA, h.symm⟩, rfl⟩
    · exact Or.inr ⟨E, ⟨hA, h⟩, rfl⟩
  show (j '' {E | E ∈ A ∧ rk E = S}).Infinite
  intro hfin'
  exact hmem ((hfin'.union hfin).subset hsplit)

/-- **Remark 1.1.** The supremum is the same for the exact-rank definition. -/
theorem sSup_RkInfExact (hne : (RkInf A j rk).Nonempty) (hbdd : BddAbove (RkInf A j rk)) :
    sSup (RkInfExact A j rk) = sSup (RkInf A j rk) := by
  have hmem := (sSup_mem_RkInfExact A j rk hne hbdd).2
  apply le_antisymm
  · exact csSup_le_csSup hbdd ⟨_, hmem⟩ (RkInfExact_subset A j rk)
  · exact le_csSup (hbdd.mono (RkInfExact_subset A j rk)) hmem

end Sets

/-! ### Theorem 1.2: transferring rank from `ℚ` to fields of degree `2ⁿ` -/

section Transfer

variable {C C' J : Type*} (AQ : Set C) (AL : Set C') (j : C → J) (j' : C' → J)
  (rk : C → ℕ) (rk' : C' → ℕ)

/-- If infinitely many `j`-invariants over `ℚ` occur with rank `≥ r` (resp. `= r`), and each such
curve has a base change in `AL` with the same `j`-invariant and rank `≥ r + m`, then
`r + m ∈ Rk^∞` of the target class. -/
theorem RkInf_transfer {r m : ℕ} (P : C → Prop)
    (hinf : (j '' {E | E ∈ AQ ∧ P E}).Infinite)
    (hbc : ∀ E ∈ AQ, P E → ∃ E' ∈ AL, j' E' = j E ∧ r + m ≤ rk' E') :
    r + m ∈ RkInf AL j' rk' := by
  refine Set.Infinite.mono ?_ hinf
  rintro _ ⟨E, ⟨hA, hP⟩, rfl⟩
  obtain ⟨E', hE', hj, hrk⟩ := hbc E hA hP
  exact ⟨E', ⟨hE', hrk⟩, hj⟩

/-- **Theorem 1.2, `sup Rk^∞_{1,T} = ∞`.** By Lemma 5.2 (1) each curve gains rank `≥ n`. -/
theorem RkInf_unbounded_transfer (n : ℕ) (hunb : ¬ BddAbove (RkInf AQ j rk))
    (hbc : ∀ E ∈ AQ, ∃ E' ∈ AL, j' E' = j E ∧ rk E + n ≤ rk' E') :
    ¬ BddAbove (RkInf AL j' rk') := by
  rintro ⟨B, hB⟩
  apply hunb
  refine ⟨B, fun r hr => ?_⟩
  have : r + n ∈ RkInf AL j' rk' :=
    RkInf_transfer AQ AL j j' rk' (fun E => r ≤ rk E) hr
      (fun E hE hle => by
        obtain ⟨E', hE', hj, h⟩ := hbc E hE
        exact ⟨E', hE', hj, by omega⟩)
  have := hB this
  omega

/-- **Theorem 1.2, `sup Rk¹_{1,T} = ∞`.** -/
theorem Rk1_unbounded_transfer (n : ℕ) (hunb : ¬ BddAbove (Rk1 AQ rk))
    (hbc : ∀ E ∈ AQ, ∃ E' ∈ AL, rk E + n ≤ rk' E') :
    ¬ BddAbove (Rk1 AL rk') := by
  rintro ⟨B, hB⟩
  apply hunb
  refine ⟨B, ?_⟩
  rintro _ ⟨E, hE, rfl⟩
  obtain ⟨E', hE', h⟩ := hbc E hE
  have := hB ⟨E', hE', rfl⟩
  omega

end Transfer

/-! ### Choosing the signs (proof of Theorem 1.2) -/

/-- The increment of Theorem 1.2: `max {2n + 2^{n-1} - 1, 2ⁿ - 1}` if `R` is odd and
`max {2n, 2^{n-1} + 2n - 2}` if `R` is even. -/
def inc (n R : ℕ) : ℕ := if Even R then incEven n else incOdd n

/-- **Proof of Theorem 1.2, the choice of signs.** Suppose that for every sign pattern
`ε₁, …, εₙ` there is a family of twists of `E` (Theorem 5.6) with `W(E^{d_k}) = ε_k`, with Parity
for the twists, with `R_{E/ℚ} = R`, and with `W(E) = (-1)^R` (Parity for `E`). Then some family has
`R_{E/L_n} ≥ R + inc n R`. -/
theorem exists_family_ge (n R : ℕ) (hn : 1 ≤ n)
    (hcon : ∀ ε : Fin n → ℤ, (∀ k, ε k = 1 ∨ ε k = -1) →
      ∃ T : TwistFamily n, T.Parity ∧ T.rank ∅ = R ∧ T.rootNumber ∅ = (-1) ^ R ∧
        ∀ k, T.rootNumber {k} = ε k) :
    ∃ T : TwistFamily n, T.Parity ∧ T.rank ∅ = R ∧ R + inc n R ≤ T.rankL := by
  have hpow : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have h2 := two_pow_eq n hn
  rcases Nat.even_or_odd R with hR | hR
  · have hW : (-1 : ℤ) ^ R = 1 := hR.neg_one_pow
    rcases le_total (2 ^ (n - 1) + 2 * n - 2) (2 * n) with hle | hle
    · -- all signs `+1`: Lemma 5.2 (4)(a)
      obtain ⟨T, hP, hR0, hW0, hk⟩ := hcon (fun _ => 1) (fun _ => Or.inl rfl)
      refine ⟨T, hP, hR0, ?_⟩
      have := T.part4a hP (hW0.trans hW) hk
      simp only [inc, ite_eq_left hR, incEven, max_eq_left hle]
      omega
    · -- `+1` for `k < n - 1` and `-1` for `k = n - 1`: Lemma 5.2 (4)(c)
      have hn2 : 2 ≤ n := by
        by_contra h
        have : n = 1 := by omega
        subst this
        norm_num at hle
      obtain ⟨T, hP, hR0, hW0, hk⟩ :=
        hcon (fun k => if k.val < n - 1 then 1 else -1)
          (fun k => by by_cases h : k.val < n - 1 <;> simp [h])
      refine ⟨T, hP, hR0, ?_⟩
      have := T.part4c hP hn2 (hW0.trans hW)
        (fun k hk' => by rw [hk k]; simp [hk'])
        (fun k hk' => by rw [hk k]; simp [show ¬ k.val < n - 1 by omega])
      simp only [inc, ite_eq_left hR, incEven, max_eq_right hle]
      omega
  · have hW : (-1 : ℤ) ^ R = -1 := hR.neg_one_pow
    have hnotE : ¬ Even R := Nat.not_even_iff_odd.mpr hR
    rcases le_total (2 ^ n - 1) (2 * n + 2 ^ (n - 1) - 1) with hle | hle
    · -- all signs `+1`: Lemma 5.2 (2)
      obtain ⟨T, hP, hR0, hW0, hk⟩ := hcon (fun _ => 1) (fun _ => Or.inl rfl)
      refine ⟨T, hP, hR0, ?_⟩
      have := T.part2 hP hn (hW0.trans hW) hk
      simp only [inc, ite_eq_right hnotE, incOdd, max_eq_left hle]
      omega
    · -- all signs `-1`: Lemma 5.2 (3)(b)
      obtain ⟨T, hP, hR0, hW0, hk⟩ := hcon (fun _ => -1) (fun _ => Or.inr rfl)
      refine ⟨T, hP, hR0, ?_⟩
      have := T.part3b hP (hW0.trans hW) hk
      simp only [inc, ite_eq_right hnotE, incOdd, max_eq_right hle]
      omega

section Main

variable {C C' J : Type*} (AQ : Set C) (AL : Set C') (j : C → J) (j' : C' → J)
  (rk : C → ℕ) (rk' : C' → ℕ)

/-- The hypotheses of Theorem 1.2 for a curve `E/ℚ` of rank `R`: for every sign pattern,
Theorem 5.6 gives a curve `E' = E ×_ℚ L_n` in the target class (field of degree `2ⁿ`, same torsion)
with the same `j`-invariant, whose rank is `R_{E/L_n} = ∑_d R_{E^d/ℚ}` (Kida), the twists satisfying
Parity, and `W(E) = (-1)^R` (Parity for `E`). -/
def BaseChangeHyp (n R : ℕ) (E : C) : Prop :=
  ∀ ε : Fin n → ℤ, (∀ k, ε k = 1 ∨ ε k = -1) →
    ∃ E' ∈ AL, j' E' = j E ∧ ∃ T : TwistFamily n, T.Parity ∧ T.rank ∅ = R ∧
      T.rootNumber ∅ = (-1) ^ R ∧ (∀ k, T.rootNumber {k} = ε k) ∧ T.rankL ≤ rk' E'

lemma baseChange_ge {n R : ℕ} (hn : 1 ≤ n) {E : C} (h : BaseChangeHyp AL j j' rk' n R E) :
    ∃ E' ∈ AL, j' E' = j E ∧ R + inc n R ≤ rk' E' := by
  -- the choice of signs of `exists_family_ge`, keeping track of the base change
  have hpow : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  rcases Nat.even_or_odd R with hR | hR
  · have hW : (-1 : ℤ) ^ R = 1 := hR.neg_one_pow
    rcases le_total (2 ^ (n - 1) + 2 * n - 2) (2 * n) with hle | hle
    · obtain ⟨E', hE', hj, T, hP, hR0, hW0, hk, hrk⟩ := h (fun _ => 1) (fun _ => Or.inl rfl)
      refine ⟨E', hE', hj, ?_⟩
      have := T.part4a hP (hW0.trans hW) hk
      simp only [inc, ite_eq_left hR, incEven, max_eq_left hle]
      omega
    · have hn2 : 2 ≤ n := by
        by_contra h'
        have : n = 1 := by omega
        subst this
        norm_num at hle
      obtain ⟨E', hE', hj, T, hP, hR0, hW0, hk, hrk⟩ :=
        h (fun k => if k.val < n - 1 then 1 else -1)
          (fun k => by by_cases h' : k.val < n - 1 <;> simp [h'])
      refine ⟨E', hE', hj, ?_⟩
      have := T.part4c hP hn2 (hW0.trans hW)
        (fun k hk' => by rw [hk k]; simp [hk'])
        (fun k hk' => by rw [hk k]; simp [show ¬ k.val < n - 1 by omega])
      simp only [inc, ite_eq_left hR, incEven, max_eq_right hle]
      omega
  · have hW : (-1 : ℤ) ^ R = -1 := hR.neg_one_pow
    have hnotE : ¬ Even R := Nat.not_even_iff_odd.mpr hR
    rcases le_total (2 ^ n - 1) (2 * n + 2 ^ (n - 1) - 1) with hle | hle
    · obtain ⟨E', hE', hj, T, hP, hR0, hW0, hk, hrk⟩ := h (fun _ => 1) (fun _ => Or.inl rfl)
      refine ⟨E', hE', hj, ?_⟩
      have := T.part2 hP hn (hW0.trans hW) hk
      simp only [inc, ite_eq_right hnotE, incOdd, max_eq_left hle]
      omega
    · obtain ⟨E', hE', hj, T, hP, hR0, hW0, hk, hrk⟩ := h (fun _ => -1) (fun _ => Or.inr rfl)
      refine ⟨E', hE', hj, ?_⟩
      have := T.part3b hP (hW0.trans hW) hk
      simp only [inc, ite_eq_right hnotE, incOdd, max_eq_right hle]
      omega

/-- **Theorem 1.2, `∗ = ∞`, `sup Rk^∞_{1,T} = R` finite.** By Remark 1.1 infinitely many
`j`-invariants occur with rank exactly `R`; if each such curve satisfies the hypotheses of
Theorem 1.2, then `R + inc n R ∈ Rk^∞_{2ⁿ,T}`, so `sup Rk^∞_{2ⁿ,T} ≥ R + inc n R`. -/
theorem thm_main1_inf (n : ℕ) (hn : 1 ≤ n) (hne : (RkInf AQ j rk).Nonempty)
    (hbdd : BddAbove (RkInf AQ j rk))
    (hbc : ∀ E ∈ AQ, rk E = sSup (RkInf AQ j rk) →
      BaseChangeHyp AL j j' rk' n (sSup (RkInf AQ j rk)) E) :
    sSup (RkInf AQ j rk) + inc n (sSup (RkInf AQ j rk)) ∈ RkInf AL j' rk' :=
  RkInf_transfer AQ AL j j' rk' (fun E => rk E = sSup (RkInf AQ j rk))
    (sSup_mem_RkInfExact AQ j rk hne hbdd).2
    (fun E hE hR => baseChange_ge AL j j' rk' hn (hbc E hE hR))

/-- **Theorem 1.2, `∗ = 1`, `sup Rk¹_{1,T} = R` finite.** The supremum is attained by a curve of
rank `R`; if it satisfies the hypotheses of Theorem 1.2, then `Rk¹_{2ⁿ,T}` has an element
`≥ R + inc n R`. -/
theorem thm_main1_one (n : ℕ) (hn : 1 ≤ n) (hne : (Rk1 AQ rk).Nonempty)
    (hbdd : BddAbove (Rk1 AQ rk))
    (hbc : ∀ E ∈ AQ, rk E = sSup (Rk1 AQ rk) →
      BaseChangeHyp AL j j' rk' n (sSup (Rk1 AQ rk)) E) :
    ∃ x ∈ Rk1 AL rk', sSup (Rk1 AQ rk) + inc n (sSup (Rk1 AQ rk)) ≤ x := by
  obtain ⟨E, hE, hrk⟩ := Nat.sSup_mem hne hbdd
  obtain ⟨E', hE', -, hle⟩ := baseChange_ge AL j j' rk' hn (hbc E hE hrk)
  exact ⟨rk' E', ⟨E', hE', rfl⟩, hle⟩

end Main

/-! ### Remark 5.9: the exact-rank dichotomy -/

/-- **Pigeonhole.** Integers `≥ b` indexed by an infinite set: either some value `≥ b` is taken
infinitely often, or the values are unbounded. -/
theorem infinite_fiber_or_unbounded {I : Type*} [Infinite I] (f : I → ℕ) (b : ℕ)
    (hb : ∀ i, b ≤ f i) :
    (∃ v, b ≤ v ∧ {i | f i = v}.Infinite) ∨ ¬ BddAbove (Set.range f) := by
  by_contra h
  push Not at h
  obtain ⟨hfin, B, hB⟩ := h
  have hcover : (Set.univ : Set I) ⊆ ⋃ v ∈ Finset.Icc b B, {i | f i = v} := by
    intro i _
    simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨f i, ⟨hb i, hB ⟨i, rfl⟩⟩, rfl⟩
  have hfinU : (⋃ v ∈ Finset.Icc b B, {i | f i = v}).Finite :=
    (Finset.Icc b B).finite_toSet.biUnion fun v hv =>
      hfin v (Finset.mem_Icc.mp hv).1
  exact Set.infinite_univ (hfinU.subset hcover)

/-- **Remark 5.9.** Let `E_i`, `i ∈ I` infinite, be curves of the class `A` with pairwise distinct
`j`-invariants and ranks `≥ b`. Then either some `R' ≥ b` lies in the exact-rank `Rk^∞`, or the
ranks in `A` are unbounded (`sup Rk¹ = ∞`). -/
theorem exact_dichotomy {C J I : Type*} [Infinite I] (A : Set C) (j : C → J) (rk : C → ℕ)
    (E : I → C) (hA : ∀ i, E i ∈ A) (hj : Function.Injective (j ∘ E)) (b : ℕ)
    (hb : ∀ i, b ≤ rk (E i)) :
    (∃ R', b ≤ R' ∧ R' ∈ RkInfExact A j rk) ∨ ¬ BddAbove (Rk1 A rk) := by
  rcases infinite_fiber_or_unbounded (rk ∘ E) b hb with ⟨v, hv, hinf⟩ | hunb
  · left
    refine ⟨v, hv, ?_⟩
    have himg : (j ∘ E) '' {i | rk (E i) = v} ⊆ j '' {E' | E' ∈ A ∧ rk E' = v} := by
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨E i, ⟨hA i, hi⟩, rfl⟩
    exact ((hinf.image hj.injOn)).mono himg
  · right
    rintro ⟨B, hB⟩
    exact hunb ⟨B, by rintro _ ⟨i, rfl⟩; exact hB ⟨E i, hA i, rfl⟩⟩

/-- **Corollary 1.4 (2), arithmetic.** `31 + max {2n + 2^{n-1} - 1, 2ⁿ - 1}
= 30 + max {2n + 2^{n-1}, 2ⁿ}`. -/
theorem cor_highrank_arith (n : ℕ) : 31 + incOdd n = 30 + max (2 * n + 2 ^ (n - 1)) (2 ^ n) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  unfold incOdd
  omega

end RankGrowth
