# Lean-LiebConcavity


A **Lean 4 / Mathlib** formalization of **Lieb's concavity theorem**, a key theorem in Quantum Information, and related results provable by same approach including Lieb's extension theorem and Ando's convexity theorem. The present approach enables the generalization towards H\*-algebra context (Ambrose 1945): a Hilbert space + normed ring + compatible star operation (motivating example: the space of n by n complex matrices endowed with Frobenius trace inner product, with star being the conjugate transpose).

Key (sorried) dependencies for the approach include: Jensen's operator inequality (*sorried*), Löwner's theorem (*sorried*), and `mul_rpow_of_commute` — the identity `(a * b) ^ r = a ^ r * b ^ r` for commuting nonneg elements in a C\*-algebra (*sorried*, requires two-variable CFC not yet in Mathlib).

Main references:

- M. Nikoufar, A. Ebadian, M. Eshaghi Gordji, *Adv. Math.* **248** (2013) 531–533
- A. Ebadian, M. Nikoufar, M. Eshaghi Gordji, *PNAS* **108** (2011) 7313–7314
- F. Hansen, G. K. Pedersen, *Bull. London Math. Soc.* **35** (2003) 553–564
- F. Hansen, G. K. Pedersen, *Math. Ann.* **258** (1982) 229–241
- Y. Li, D. Wu, *J. Operator Theory* **67** (2012) 329–337

## Structure

| File | Contents |
|------|----------|
| `Defs.lean` | `OperatorConvexOn`/`OperatorConcaveOn`; `GenPerspective`; `GenPerspective_of_commute` (*done*); `GenPerspective_of_rpow_commute` (*done, pending* `mul_rpow_of_commute`) |
| `HStarAlgebra.lean` | H\*-algebra typeclass; `Lmul`/`Rmul` as star-algebra homs (*done*); CFC commutativity for both `Lmul` and `Rmul` (*done*) |
| `Jensen.lean` | Jensen's operator inequality (*sorried*) |
| `Main.lean` | Lieb concavity + Lieb extension + Ando convexity (*todo*) |
| `ForMathlib.lean` | Lemmas not yet in Mathlib: `Commute.rpow_right/left/rpow`, `mul_rpow_of_commute` (*sorried*), `cfc_isStrictlyPositive_of_pos/nonneg`, `MulOppositeStarAlgEquiv` |
| `MulOppositeStarAlgEquiv.lean` | `starAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ`; `opStar`; CFC and rpow commutativity across `op` (*done*) |

## Building

Requires a compatible Lean 4 toolchain (see `lean-toolchain`).

```bash
lake build
