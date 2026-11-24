# Lean formalization

A Lean 4 / Mathlib formalization of the combinatorial and elementary number-theoretic core of

> D. T. Costa and Á. Lozano-Robledo, *Rank Growth in Quadratic Extensions using Twists* (v9).

Result numbers below refer to v9 of the paper.

## Build

Lean `v4.34.0` (`lean-toolchain`). Mathlib is pinned to revision `db00fb3901b1bb4954f8a2373285959a5930bbfa` (`lakefile.toml`, `lake-manifest.json`).

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

`lake build` finishes with no errors and no warnings. The sources contain no `sorry`, `admit`, `axiom` or `native_decide`.

`AxiomCheck.lean` prints the axioms used by each of the results below. Every result uses only Lean's standard axioms, `propext`, `Classical.choice` and `Quot.sound`. Some don't need `Classical.choice`.

## What is formalized

| Paper | Lean (`RankGrowth.…`) |
|---|---|
| Remark 1.1, $\mathrm{Rk}^\infty_{d,T}$ is closed downwards | `RkInf_downward` |
| Remark 1.1, a finite $S=\sup(\mathrm{Rk}^\infty_{d,T})$ lies in $\mathrm{Rk}^\infty_{d,T}$, is attained with rank exactly $S$, and is also the supremum for the exact-rank definition | `sSup_mem_RkInfExact`, `sSup_RkInfExact` |
| Theorem 1.2, case $\sup(\mathrm{Rk}^\ast_{1,T})=\infty$ | `RkInf_unbounded_transfer`, `Rk1_unbounded_transfer` |
| Theorem 1.2, the choice of signs | `exists_family_ge` |
| Theorem 1.2, case $\sup(\mathrm{Rk}^\ast_{1,T})=R$ finite, for $\ast=\infty$ and $\ast=1$ | `thm_main1_inf`, `thm_main1_one` |
| Corollary 1.4 (2), $31+\max\{2n+2^{n-1}-1,2^n-1\}=30+\max\{2n+2^{n-1},2^n\}$ | `cor_highrank_arith` |
| Eq. (5), from Lemma 4.6 and the multiplicativity of the Kronecker symbol | `rootNumber_product` |
| Corollary 4.7 | `rootNumber_full_product` |
| Corollary 4.15 (the deduction from Theorem 4.14) | `parity_of_pparity` |
| Lemma 5.2 (1) | `TwistFamily.part1` |
| Lemma 5.2 (2) | `TwistFamily.part2` |
| Lemma 5.2 (3), $W(E^d)=-1$ for all $d\in\mathcal D_n$ | `TwistFamily.part3_rootNumber` |
| Lemma 5.2 (3)(a) | `TwistFamily.part3a` |
| Lemma 5.2 (3)(b), under Parity and under BSD | `TwistFamily.part3b`, `TwistFamily.part3b_bsd` |
| Lemma 5.2 (4)(a), (b), (c) | `TwistFamily.part4a`, `part4b`, `part4c` |
| Lemma 5.4, $f(x_1/M^2) = F/M^6$ | `f_eval_eq` |
| Lemma 5.4, the Legendre symbols of $F$ and of $d_0$ at the $p_i$ and the $q_j$ | `legendreSym_F`, `legendreSym_F_eq_one`, `legendreSym_F_eq_neg_one`, `legendreSym_mul_sq`, `legendreSym_d0_eq_one`, `legendreSym_d0_eq_neg_one` |
| Lemma 5.4, $d_0$ is not a square | `legendreSym_d0_eq_neg_one` |
| Lemma 5.4, $d_0 \equiv 1 \bmod 8$ | `numF_modEq_one_eight`, `d0_modEq_one_eight` |
| Lemma 5.4, the sign of $d_0$ | `numF_pos`, `numF_neg`, `d0_pos`, `d0_neg` |
| Remark 5.7, no product of the $d_k$ is a square | `prod_not_isSquare` |
| Remark 5.7, the square-free part of $\prod_{k\in S}d_k$ is $\equiv 1 \bmod 8$, prime to $210N_E$, not $\pm1$, and has a prime factor $\ell\nmid 210N_E$ | `sqfree_part_prod` |
| Remark 5.8, the bound (4)(c) is at least (4)(a) for $n\ge2$, with equality for $n=2$, and larger than (4)(b) | `bound4a_le_bound4c`, `bound4a_eq_bound4c_two`, `bound4b_lt_bound4c` |
| Remark 5.8, $W(E^d)=-1$ iff $\lvert S\setminus P\rvert$ is odd ($W(E)=1$), iff $\lvert S\cap P\rvert$ is even ($W(E)=-1$) | `TwistFamily.rootNumber_eq_neg_one_iff_plus`, `rootNumber_eq_neg_one_iff_minus` |
| Remark 5.8, the bound for every sign pattern | `TwistFamily.signPattern_plus`, `signPattern_minus` |
| Remark 5.8 and Theorem 1.2, the increments are the largest such bounds and are attained | `countPlus_le`, `countMinus_le`, `incEven_attained`, `incOdd_attained` |
| Remark 5.9, the exact-rank dichotomy (pigeonhole) | `infinite_fiber_or_unbounded`, `exact_dichotomy` |

All parts of Lemma 5.2 come out of one counting inequality, `TwistFamily.two_mul_sum_ge`, together with the identity
$\sum_{S} W(E^{d_S}) = W(E)\prod_k \bigl(1 + W(E)\,W(E^{d_k})\bigr)$ (`sum_rootNumbers`).

## How the rank sets are modeled (`RankGrowth/RankSets.lean`)

A class of elliptic curves (for example all $E/L$ with $[L:\mathbb Q]=d$ and $E(L)_{\mathrm{tors}}\cong T$) is a set `A` in a type of curves, with a $j$-invariant `j` and a rank `rk`. Two curves are geometrically isomorphic iff they have the same $j$-invariant. So "infinitely many pairwise geometrically non-isomorphic curves" becomes "infinitely many $j$-invariants".

* `Rk1 A rk` is $\mathrm{Rk}^1_{d,T}$, the set of ranks of curves in `A`.
* `RkInf A j rk` is $\mathrm{Rk}^\infty_{d,T}$, the set of $R$ such that infinitely many $j$-invariants occur with rank $\ge R$.
* `RkInfExact A j rk` is the same with rank exactly $R$.

For Theorem 1.2, `BaseChangeHyp` packages what the paper takes from Theorem 5.6, Proposition 4.5 and the Parity Conjecture for a curve $E/\mathbb Q$ of rank $R$. For every choice of signs, there is a curve $E\times_{\mathbb Q}L_n$ in the target class (degree $2^n$, same torsion) with the same $j$-invariant. Its rank is at least $\sum_d R_{E^d/\mathbb Q}$ for a `TwistFamily` with those signs, Parity for the twists, and $W(E)=(-1)^R$.

## What is assumed

Mathlib does not yet have Mordell–Weil ranks over number fields, root numbers, or $L$-functions of elliptic curves. The results the paper cites therefore enter as **explicit hypotheses**, never as axioms. A `TwistFamily n` records the ranks $R_{E^{d_S}/\mathbb Q}$ and root numbers $W(E^{d_S})$ for $S \subseteq \{1,\dots,n\}$.

* **Kida's formula (Proposition 4.5)** is the definition `TwistFamily.rankL`, $R_{E/L_n} = \sum_{d\in\mathcal D_n} R_{E^d/\mathbb Q}$, which is Eq. (4).
* **Dokchitser's formula (Lemma 4.6)** is the hypothesis `hkron` of `rootNumber_product`. Its consequence, Eq. (5), is the field `TwistFamily.rootNumber_mul`.
* **The Parity Conjecture (Conjecture 4.3)** is the hypothesis `TwistFamily.Parity`. It can be replaced by the finiteness of $\mathrm{Sha}(E^d/\mathbb Q)[p^\infty]$ together with the $p$-parity theorem (Theorem 4.14), via `parity_of_pparity`.
* **Theorem 4.11 (Gross–Zagier, Kolyvagin) and BSD** enter Lemma 5.2 (3)(a) and (3)(b) as hypotheses on the ranks.
* **Theorem 5.6 is not formalized.** It uses Mordell–Weil, Fujita and Najman. Its arithmetic ingredients, Lemma 5.4 and Remark 5.7, are formalized. Its conclusions (fields of degree $2^n$ with prescribed signs, no torsion growth) enter Theorem 1.2 through `BaseChangeHyp`.
* **Base change keeps the $j$-invariant.** This is part of `BaseChangeHyp`.
* **Kummer theory is not formalized.** This is the step from "no product of the $d_k$ is a square" to $[\mathbb Q(\sqrt{d_1},\dots,\sqrt{d_n}):\mathbb Q]=2^n$.
