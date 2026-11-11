# Lean formalization

A Lean 4 / Mathlib formalization of the combinatorial and elementary number-theoretic core of

> D. T. Costa and Á. Lozano-Robledo, *Elliptic curve rank growth in multi-quadratic extensions*.

Result numbers below refer to the paper.

## Build

Lean `v4.34.0` (`lean-toolchain`). Mathlib is pinned to revision `db00fb3901b1bb4954f8a2373285959a5930bbfa` (`lakefile.toml`, `lake-manifest.json`).

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

`lake build` finishes with no errors and no warnings. The sources contain no `sorry`, `admit`, `axiom` or `native_decide`.

`AxiomCheck.lean` prints the axioms used by each of the results below. Every result uses only Lean's standard axioms, `propext`, `Classical.choice` and `Quot.sound`. The two `attained` lemmas don't need `Classical.choice`.

## What is formalized

| Paper | Lean (`RankGrowth.…`) |
|---|---|
| Eq. (5), from Lemma 4.6 and the multiplicativity of the Kronecker symbol | `rootNumber_product` |
| Corollary 4.7 | `rootNumber_full_product` |
| Corollary 4.14 (the deduction from Theorem 4.13) | `parity_of_pparity` |
| Lemma 5.2 (1) | `TwistFamily.part1` |
| Lemma 5.2 (2) | `TwistFamily.part2` |
| Lemma 5.2 (3), $W(E^d)=-1$ for all $d\in\mathcal D_n$ | `TwistFamily.part3_rootNumber` |
| Lemma 5.2 (3)(a) | `TwistFamily.part3a` |
| Lemma 5.2 (3)(b), under Parity and under BSD | `TwistFamily.part3b`, `TwistFamily.part3b_bsd` |
| Lemma 5.2 (4)(a), (b), (c) | `TwistFamily.part4a`, `part4b`, `part4c` |
| Remark 5.8, the bound for every sign pattern | `TwistFamily.signPattern_plus`, `signPattern_minus` |
| Remark 5.8 and Theorem 1.1, the increments are the largest such bounds and are attained | `countPlus_le`, `countMinus_le`, `incEven_attained`, `incOdd_attained` |
| Lemma 5.4, $f(x_1/M^2) = F/M^6$ | `f_eval_eq` |
| Lemma 5.4, the Legendre symbols at the $p_i$ and the $q_j$ | `legendreSym_F`, `legendreSym_F_eq_one`, `legendreSym_F_eq_neg_one`, `legendreSym_mul_sq` |
| Lemma 5.4, $d_0 \equiv 1 \bmod 8$ | `numF_modEq_one_eight` |
| Lemma 5.4, the sign of $d_0$ | `numF_pos`, `numF_neg` |
| Remark 5.7, no product of the $d_k$ is a square | `prod_not_isSquare` |

All parts of Lemma 5.2 come out of one counting inequality, `TwistFamily.two_mul_sum_ge`, together with the identity
$\sum_{S} W(E^{d_S}) = W(E)\prod_k \bigl(1 + W(E)\,W(E^{d_k})\bigr)$ (`sum_rootNumbers`).

## What is assumed

Mathlib does not yet have Mordell–Weil ranks over number fields, root numbers, or $L$-functions of elliptic curves. The results the paper cites therefore enter as **explicit hypotheses**, never as axioms. A `TwistFamily n` records the ranks $R_{E^{d_S}/\mathbb Q}$ and root numbers $W(E^{d_S})$ for $S \subseteq \{1,\dots,n\}$.

* **Kida's formula (Proposition 4.5)** is the definition `TwistFamily.rankL`, $R_{E/L_n} = \sum_{d\in\mathcal D_n} R_{E^d/\mathbb Q}$, which is Eq. (4).
* **Dokchitser's formula (Lemma 4.6)** is the hypothesis `hkron` of `rootNumber_product`. Its consequence, Eq. (5), is the field `TwistFamily.rootNumber_mul`.
* **The Parity Conjecture (Conjecture 4.3)** is the hypothesis `TwistFamily.Parity`. It can be replaced by the finiteness of $\mathrm{Sha}(E^d/\mathbb Q)[p^\infty]$ together with the $p$-parity theorem (Theorem 4.13), via `parity_of_pparity`.
* **Theorem 4.10 (Gross–Zagier, Kolyvagin) and BSD** enter Lemma 5.2 (3)(a) and (3)(b) as hypotheses on the ranks.
* **Theorem 5.6 is not formalized.** It uses Mordell–Weil, Fujita and Najman. Its arithmetic ingredients, Lemma 5.4 and Remark 5.7, are formalized.
* **Kummer theory is not formalized.** This is the step from "no product of the $d_k$ is a square" to $[\mathbb Q(\sqrt{d_1},\dots,\sqrt{d_n}):\mathbb Q]=2^n$.
