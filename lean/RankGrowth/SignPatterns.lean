import RankGrowth.MultiquadraticRank

/-!
# The best sign pattern: Remark `rem-signpatterns` and Theorem `thm-main1`

Costa, Lozano-Robledo, *Rank growth in quadratic extensions using twists*.

`TwistFamily.bound_plus` and `TwistFamily.bound_minus` give, for `p` = the number of `k` with
`W(E^{d_k}) = +1`, the lower bound `countPlus n p` (if `W(E) = +1`) or `countMinus n p`
(if `W(E) = -1`) for `R_{E/L_n} - R_{E/ℚ}`. Here we show that, over all `0 ≤ p ≤ n`, the largest
of these bounds is `max {2n, 2^{n-1} + 2n - 2}`, respectively `max {2n + 2^{n-1} - 1, 2ⁿ - 1}`,
which are the increments in Theorem `thm-main1`, and that they are attained by the sign patterns
of Lemma `lem:multiquadratic-rank` (4)(a), (4)(c), (2) and (3).
-/

namespace RankGrowth

/-- The counting bound when `W(E) = +1` and `p` of the `W(E^{d_k})` are `+1`. -/
def countPlus (n p : ℕ) : ℕ := if p = n then 2 * n else 2 ^ (n - 1) + 2 * p

/-- The counting bound when `W(E) = -1` and `p` of the `W(E^{d_k})` are `+1`. -/
def countMinus (n p : ℕ) : ℕ := if p = 0 then 2 ^ n - 1 else 2 ^ (n - 1) - 1 + 2 * p

/-- The increment in Theorem `thm-main1` (2), `sup Rk_{1,T}` even (`W(E) = +1`). -/
def incEven (n : ℕ) : ℕ := max (2 * n) (2 ^ (n - 1) + 2 * n - 2)

/-- The increment in Theorem `thm-main1` (1), `sup Rk_{1,T}` odd (`W(E) = -1`). -/
def incOdd (n : ℕ) : ℕ := max (2 * n + 2 ^ (n - 1) - 1) (2 ^ n - 1)

lemma two_pow_eq (n : ℕ) (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']
  congr 1
  omega

theorem countPlus_le (n p : ℕ) (hp : p ≤ n) : countPlus n p ≤ incEven n := by
  unfold countPlus incEven
  split_ifs with h
  · exact le_max_left _ _
  · exact le_max_of_le_right (by omega)

theorem countMinus_le (n p : ℕ) (hn : 1 ≤ n) (hp : p ≤ n) : countMinus n p ≤ incOdd n := by
  unfold countMinus incOdd
  have h2 := two_pow_eq n hn
  have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  split_ifs with h
  · exact le_max_right _ _
  · exact le_max_of_le_left (by omega)

/-- The maximum `incEven n` is attained: by `p = n` (Lemma (4)(a)) or `p = n - 1` (Lemma (4)(c)). -/
theorem incEven_attained (n : ℕ) (hn : 1 ≤ n) :
    incEven n = countPlus n n ∨ incEven n = countPlus n (n - 1) := by
  unfold incEven countPlus
  rw [ite_eq_left rfl, ite_eq_right (by omega)]
  rcases le_total (2 * n) (2 ^ (n - 1) + 2 * n - 2) with h | h
  · right
    rw [max_eq_right h]
    have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  · left
    exact max_eq_left h

/-- The maximum `incOdd n` is attained: by `p = n` (Lemma (2)) or `p = 0` (Lemma (3)). -/
theorem incOdd_attained (n : ℕ) (hn : 1 ≤ n) :
    incOdd n = countMinus n n ∨ incOdd n = countMinus n 0 := by
  unfold incOdd countMinus
  rw [ite_eq_right (by omega), ite_eq_left rfl]
  have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  rcases le_total (2 * n + 2 ^ (n - 1) - 1) (2 ^ n - 1) with h | h
  · right
    exact max_eq_right h
  · left
    rw [max_eq_left h]
    omega

namespace TwistFamily

variable {n : ℕ} (T : TwistFamily n)

/-- **Remark `rem-signpatterns`, `W(E) = +1`.** Under Parity, for any signs,
`R_{E/L_n} ≥ R_{E/ℚ} + countPlus n p`, and `countPlus n p ≤ max {2n, 2^{n-1} + 2n - 2}`. -/
theorem signPattern_plus (hP : T.Parity) (h0 : T.rootNumber ∅ = 1) :
    T.rank ∅ + countPlus n T.numPlus ≤ T.rankL := by
  have := T.bound_plus hP h0
  rw [T.rankL_eq]
  unfold countPlus
  omega

/-- **Remark `rem-signpatterns`, `W(E) = -1`.** Under Parity, for any signs,
`R_{E/L_n} ≥ R_{E/ℚ} + countMinus n p`, and `countMinus n p ≤ max {2n + 2^{n-1} - 1, 2ⁿ - 1}`. -/
theorem signPattern_minus (hP : T.Parity) (h0 : T.rootNumber ∅ = -1) :
    T.rank ∅ + countMinus n T.numPlus ≤ T.rankL := by
  have := T.bound_minus hP h0
  rw [T.rankL_eq]
  unfold countMinus
  omega

/-! ### Remark 5.8: which twists have root number `-1` -/

/-- `∏_{k ∈ S} W(E^{d_k}) = (-1)^{|S \ P|}`, `P = {k : W(E^{d_k}) = +1}`. -/
lemma prod_rootNumber_singleton (S : Finset (Fin n)) :
    ∏ k ∈ S, T.rootNumber {k} =
      (-1) ^ (S \ Finset.univ.filter fun k => T.rootNumber {k} = 1).card := by
  classical
  have hdiff : (S \ Finset.univ.filter fun k => T.rootNumber {k} = 1)
      = S.filter fun k => ¬ T.rootNumber {k} = 1 := by
    ext k; simp
  rw [hdiff, ← Finset.prod_filter_mul_prod_filter_not S (fun k => T.rootNumber {k} = 1)]
  rw [Finset.prod_eq_one (fun k hk => (Finset.mem_filter.mp hk).2), one_mul]
  rw [Finset.prod_congr rfl (fun k hk => (T.rootNumber_sign {k}).resolve_left
    (Finset.mem_filter.mp hk).2), Finset.prod_const]

lemma neg_one_pow_eq_neg_one_iff (a : ℕ) : (-1 : ℤ) ^ a = -1 ↔ Odd a := by
  rcases Nat.even_or_odd a with h | h
  · rw [h.neg_one_pow]
    simp only [show ¬ Odd a from Nat.not_odd_iff_even.mpr h, iff_false]
    norm_num
  · simp [h.neg_one_pow, h]

/-- **Remark 5.8, `W(E) = +1`.** `W(E^{d_S}) = -1` iff `|S \ P|` is odd. -/
theorem rootNumber_eq_neg_one_iff_plus (h0 : T.rootNumber ∅ = 1) (S : Finset (Fin n)) :
    T.rootNumber S = -1 ↔
      Odd (S \ Finset.univ.filter fun k => T.rootNumber {k} = 1).card := by
  rw [T.rootNumber_mul S, h0, one_pow, one_mul, T.prod_rootNumber_singleton,
    neg_one_pow_eq_neg_one_iff]

/-- **Remark 5.8, `W(E) = -1`.** `W(E^{d_S}) = -1` iff `|S ∩ P|` is even. -/
theorem rootNumber_eq_neg_one_iff_minus (h0 : T.rootNumber ∅ = -1) (S : Finset (Fin n)) :
    T.rootNumber S = -1 ↔
      Even (S ∩ Finset.univ.filter fun k => T.rootNumber {k} = 1).card := by
  classical
  have hcard : (S ∩ Finset.univ.filter fun k => T.rootNumber {k} = 1).card
      + (S \ Finset.univ.filter fun k => T.rootNumber {k} = 1).card = S.card := by
    rw [add_comm]; exact Finset.card_sdiff_add_card_inter _ _
  rw [T.rootNumber_mul S, h0, T.prod_rootNumber_singleton, ← pow_add,
    neg_one_pow_eq_neg_one_iff]
  constructor
  · intro h
    by_contra he
    rw [Nat.not_even_iff_odd] at he
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := h
    omega
  · intro h
    obtain ⟨a, ha⟩ := h
    exact ⟨a + (S \ Finset.univ.filter fun k => T.rootNumber {k} = 1).card, by omega⟩

end TwistFamily

/-! ### Remark 5.8: comparing the bounds of Lemma 5.2 (4) -/

/-- **Remark 5.8.** For `n ≥ 2` the bound of (4)(c) is at least that of (4)(a). -/
theorem bound4a_le_bound4c (n : ℕ) (hn : 2 ≤ n) : 2 * n ≤ 2 ^ (n - 1) + 2 * n - 2 := by
  have : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Remark 5.8.** Equality for `n = 2`. -/
theorem bound4a_eq_bound4c_two : 2 * 2 = 2 ^ (2 - 1) + 2 * 2 - 2 := by norm_num

/-- **Remark 5.8.** For `n ≥ 2` the bound of (4)(c) is larger than that of (4)(b). -/
theorem bound4b_lt_bound4c (n : ℕ) (hn : 2 ≤ n) : 2 ^ (n - 1) < 2 ^ (n - 1) + 2 * n - 2 := by
  omega

end RankGrowth
