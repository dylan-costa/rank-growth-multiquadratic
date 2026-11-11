# Elliptic curve rank growth in multi-quadratic extensions

Magma code and data for

> D. T. Costa and Á. Lozano-Robledo, *Elliptic curve rank growth in multi-quadratic extensions*.

<!-- TODO: add the arXiv link once the paper is posted. -->

For an elliptic curve $E/\mathbb{Q}$ and a sign $\varepsilon = \pm 1$, the paper constructs explicit square-free integers $d_1, d_2, \ldots$ with these properties:

- each twist $E^{d_k}$ has root number $\varepsilon$ and an explicit point of infinite order;
- $\mathbb{Q}(\sqrt{d_1}, \ldots, \sqrt{d_n})$ has degree $2^n$;
- the torsion of $E$ does not grow over this field.

Under the Parity Conjecture this gives lower bounds for the rank of $E$ over multi-quadratic fields. These are applied to the record curves of rank 32 and 31.

## Files

| File | Contents |
|---|---|
| `EllipticRankTwists.m` | The two algorithms of Section 6: `NaiveRootNumberTwistSearch` and `ConstructRootNumberTwists` (the construction of Remark 5.7 / Theorem 5.6). |
| `HighRankCurves.m` | The record curves of Section 2 ($E_{32}$, $E_{31}$, $E'_{31}$, $E_{30}$, $E_{29}$, $E_{28}$, $E_{17}$), with their bad primes, conductors and root numbers. |
| `verify-paper.m` | Checks the numerical claims of the paper outside Section 6 (see below). |
| `verify-paper.out` | The output of `verify-paper.m`, for comparison. |
| `lean/` | A Lean 4 / Mathlib formalization of Lemma 5.2, Remark 5.8 (and the optimality of the bounds in Theorem 1.1), Lemma 5.4 and Remark 5.7. See `lean/README.md`. |

## Usage

Magma's `-b` flag only suppresses the banner. Every script here ends with `quit;`, so it exits when it is done.

```
load "EllipticRankTwists.m";
E := EllipticCurve([0, 0, 0, 0, -2]);                       // y^2 = x^3 - 2

// Naive search: twists E^{f(x)}, |x| <= 10, with root number +1
best, all := NaiveRootNumberTwistSearch(E, 10 : keep := 10);

// The construction: d_1, d_2, d_3 with W(E^{d_k}) = +1
ds, recs := ConstructRootNumberTwists(E, 1 : howmany := 3);
recs[1]`P;                                                  // point of infinite order on E^{d_1}
```

For the record curves, pass the root number and the bad primes, so that Magma never has to compute a conductor:

```
load "EllipticRankTwists.m";
load "HighRankCurves.m";
ds, recs := ConstructRootNumberTwists(E32, 1 : howmany := 3,
                                      W := E32_W, BadPrimes := E32_BadPrimes);
```

For these curves $d_k$ has more than 1000 digits and cannot be fully factored, so `recs[k]`dProven` is `false`. The square class of $d_k$ is still exact, and so are the twist $E^{d_k}$ and its root number. See the comments in `EllipticRankTwists.m`.

## What `verify-paper.m` checks

Run `magma -b verify-paper.m` from this folder. Each check prints `PASS` or `FAIL`, and a summary is printed at the end.

1. **The record curves (Theorems 2.1–2.6, Example 4.4, Corollary 1.3).** For each curve:
   - every listed bad prime is prime;
   - the discriminant has no other prime factor, so the list is complete;
   - the conductor is the stated one;
   - the root number equals the product of the local root numbers.

   This covers $W(E_{32}) = +1$ and $W(E'_{31}) = -1$, which Corollary 1.3 uses. It also checks the factorization of $N_{E_{32}}$, its Kodaira types and its local root numbers (Example 4.4).
2. **Theorem 2.7:** $E_{17}$ has trivial torsion over $\mathbb{Q}(\sqrt{-3})$, $E_{17}^{-3}$ is isogenous to $E_{17}$, and $W(E_{17}) = -1$.
3. **Example 2.10** ($y^2 = x^3 - 2$):
   - the twists of rank 0, 1 and 2 that the example lists;
   - the ranks over the three triquadratic fields;
   - the root-number pattern;
   - the twists $d_1, d_2, d_3$.
4. **Example 2.11** ($y^2 = x^3 - x^2 - 9x + 9$):
   - $N_E$, $W(E)$, the torsion and the ranks of the twists;
   - rank 12 over $\mathbb{Q}(\sqrt{15}, \sqrt{-35}, \sqrt{-47})$, with torsion $\mathbb{Z}/2 \times \mathbb{Z}/2$ there and $\mathbb{Z}/2 \times \mathbb{Z}/4$ over $\mathbb{Q}(\sqrt{-2})$;
   - the twists $d_1, d_2, d_3$.
5. **Example 2.12** ($y^2 = x(x-2)(x+3)$):
   - the torsion over $\mathbb{Q}(\sqrt2, \sqrt5)$ and over $\mathbb{Q}(i, \sqrt2, \sqrt3, \sqrt5)$;
   - no torsion growth over any quadratic field.
6. **Example 4.2** (390.c4): conductor, reduction types, root number and rank.
7. **Corollary 5.1, Theorem 1.1, Corollary 1.3:**
   - $5040$ is the lcm of the exponents of the 20 groups of Theorem 3.3;
   - the inequalities that decide the maxima.
8. **Section 7:** the properties of Mestre's polynomial $g(t)$, and that $P(t), Q(t)$ lie on $E^{g(t)}$ for generic $a, b$.

All ranks are proved with `RankBounds` (the lower and upper bounds agree), and no class group bounds are assumed, so they do not depend on GRH. Example 6.1 and the table at the end of Section 6 are outputs of the algorithms: run the commands quoted there after `load "EllipticRankTwists.m";`.

`verify-paper.out` was produced with Magma V2.25-3.

## Lean formalization

The folder `lean/` formalizes the combinatorial and elementary number-theoretic core of the paper in Lean 4 with Mathlib: every part of Lemma 5.2, the sign-pattern bounds of Remark 5.8 and the optimality of the increments in Theorem 1.1, and the arithmetic of Lemma 5.4 and Remark 5.7. The results the paper cites (Kida's formula, Dokchitser's root-number formula, the Parity Conjecture or $p$-parity, Gross–Zagier–Kolyvagin, BSD) are not in Mathlib, so they enter as explicit hypotheses, never as axioms. To check it, run `lake exe cache get && lake build` in `lean/`; `lean/README.md` maps each result to its Lean name and lists exactly what is assumed.

## Related

The quadratic twist of $E_{32}$ of rank $\ge 2$ and root number $-1$ (Remark 2.8 and Section 7) has its own code and data repository: <https://github.com/alozanoroble/rank35>.

## Contact

Dylan T. Costa (dylan.costa@uconn.edu) and Álvaro Lozano-Robledo (alvaro.lozano-robledo@uconn.edu), University of Connecticut.
