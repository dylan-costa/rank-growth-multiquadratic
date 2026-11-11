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

end TwistFamily

end RankGrowth
