# Lean-LiebConcavity

This is a **Lean 4** formalization of **Lieb's concavity theorem**, a key result in
quantum information theory, together with its relatives Lieb's extension theorem and Ando's convexity
theorem. The formalization follows the paper [Simplest proof of Lieb Concavity Theorem](https://www.sciencedirect.com/science/article/pii/S0001870813003010). This paper depends a couple of results in the topic of [perspective functions](https://www.pnas.org/doi/10.1073/pnas.1102518108), which in turn depends on [operator Jensen's inequality](https://link.springer.com/article/10.1007/BF01450679), but we follow [this](https://link.springer.com/article/10.1007/s10114-013-2065-8) that generalizes Jensen to any unital C\*-algebra.

Modulo two sorries, all main theorems are now formalized. We also managed to prove Lieb in the generality of [H\*-algebra](https://www.jstor.org/stable/1990182) — a Hilbert space equipped with a compatible star operation and is a normed ring. This generalizes the space of n by n complex matrices with Frobenius inner product and conjugate-transpose star. As matrices in Mathlib don't come equipped with canonical inner product/norm, we provided independent packaging of the necessary ad hoc typeclass instantiations (and we did this too in the proof of Jensen, in which we need CStarAlgebra instance on matrix types).

## References

- I. Nikoufar, A. Ebadian, M. E. Gordji, *The simplest proof of Lieb concavity theorem*,
  Adv. Math. **248** (2013) 531–533
- A. Ebadian, I. Nikoufar, M. E. Gordji, *Perspectives of matrix convex functions*,
  PNAS **108** (2011) 7313–7314
- F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. **258** (1982) 229–241
- X. Li, W. Wu, *Operator Jensen's inequality on C⋆-algebras*,
  Act. Math. Sinica **30** (2013) 35–50
- E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*,
  Adv. Math. **11** (1973) 267–288
- K. Löwner, *Über monotone Matrixfunktionen*,
  Math. Z. **38** (1934) 177–216
- W. Ambrose, *Structure theorems for a special class of Banach algebras*,
  Trans. AMS **57** (1945) 364–386

## Structure

### Core

- **`Defs.lean`** — Core definitions: operator convexity/concavity, the generalized perspective function, and the operator power mean.
- **`HStarAlgebra.lean`** — The H\*-algebra typeclass defined. Bundled left/right multiplication as star-algebra homomorphisms into the CLM, thus proved they commute with CFC, and specialized to taking rpow.
- **`ConjugateWeightedSum.lean`** — Supports Jensen. It also has the potential to be further developed as non-commutative analogue of convex combination.
- **`Jensen.lean`** — Jensen's operator inequality for operator convex functions on any unital C\*-algebra, following Li–Wu via a block-matrix unitary argument. Includes sub-unital and concave variants.
- **`Main.lean`** — Joint convexity/concavity of the generalized perspective function and the operator power mean. Also records the sorried Löwner-theorem statements that `x ↦ x ^ r` is operator convex for `1 ≤ r ≤ 2` and operator concave for `0 < r ≤ 1`.
- **`Lieb.lean`** — `LiebConcavity`, `LiebExtension`, and `AndoConvexity` in the abstract H\*-algebra setting, plus matrix specializations.

### Mathlib candidates (`ForMathlib/`)

Lemmas missing from Mathlib, organized by topic.

- **`Continuity.lean`** — Continuity of `rpow` on the positive reals.
- **`SelfAdjoint.lean`** — Missing self-adjointness lemmas.
- **`CStarMatrix.lean`** — Auxiliary `ofMatrix` lemmas for `CStarMatrix`.
- **`InnerProductSpace/Positive.lean`** —  Missing monotonicity lemmas for inner product.
- **`Frobenius/Inner.lean`** — Frobenius inner product `⟪X, Y⟫ = (Y * Xᴴ).trace` on `Matrix n n 𝕜` and its basic properties.
- **`Frobenius/Matrix.lean`** — All typeclass instances needed by `HStarAlgebra 𝕜` on `Matrix n n 𝕜` with Frobenius norm and Loewner order, scoped under the `FrobeniusMat` namespace.
- **`ContinuousFunctionalCalculus/Unital.lean`** — Characterization of nonnegativity via spectrum for self-adjoint elements.
- **`ContinuousFunctionalCalculus/Order.lean`** — Strict positivity lemmas (`isUnit_of_le`, `isStrictlyPositive_of_le`) not requiring `CStarAlgebra`, only CFC and `NonnegSpectrumClass`.
- **`ContinuousFunctionalCalculus/Commute.lean`** — CFC applied to commuting elements: `cfc f a` commutes with `cfc g a`.
- **`ContinuousFunctionalCalculus/Rpow.lean`** — Missing rpow identities and commutativity lemmas.
- **`ContinuousFunctionalCalculus/Convex.lean`** — Convexity of the set of strictly positive elements; spectrum of convex combinations of self-adjoint elements.
- **`StarAlgHom/Diagonal.lean`** — `Matrix.diagonal` upgraded to a `StarAlgHom`; CFC on diagonal matrices; C\*-algebra instances on `Matrix n n A` scoped under `MatCStar`.
- **`StarAlgHom/Unitary.lean`** — CFC commutes with unitary conjugation, at both general and C\*-algebra levels.
- **`StarAlgHom/OpStar.lean`** — Bundled the map `a ↦ op(star a)` as a star-algebra equivalence `A ≃⋆ₐ[R] Aᵐᵒᵖ`; CFC and rpow commutativity across `MulOpposite`.

## Sorries

| Declaration | File | Reason |
|-------------|------|--------|
| `mul_rpow_of_commute` | `ForMathlib/ContinuousFunctionalCalculus/Rpow.lean` | Requires two-variable CFC not yet in Mathlib |
| `CFC.rpow_operatorConvexOn` | `Main.lean` | Requires Löwner's theorem |
| `CFC.rpow_operatorConcaveOn` | `Main.lean` | Requires Löwner's theorem |

## Building

Requires Lean `v4.29.0-rc6` (see `lean-toolchain`).

```bash
lake exe cache get   # fetch Mathlib build cache
lake build
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
