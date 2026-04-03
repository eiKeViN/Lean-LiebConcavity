# Lean-LiebConcavity


A **Lean 4 / Mathlib** formalization of **Lieb's concavity theorem**, a key theorem in Quantum Information, and related results provable by same approach including Lieb's extension theorem and Ando's convexity theorem. The present approach enables the generalization towards H\*-algebra context (Ambrose 1945): a Hilbert space + normed ring + compatible star operation (motivating example: the space of n by n complex matrices endowed with Frobenius trace inner product, with star being the conjugate transpose).

The main theorems — `LiebConcavity` [Thm 1.2(a)], `LiebExtension` [Thm 1.2(b)], and `AndoConvexity` [Thm 1.4] — are proved in full generality for any H\*-algebra satisfying appropriate order axioms. Key (sorried) dependencies include: Jensen's operator inequality (*sorried*), Löwner's theorem (*sorried*), and `mul_rpow_of_commute` — the identity `(a * b) ^ r = a ^ r * b ^ r` for commuting nonneg elements in a C\*-algebra (*sorried*, requires two-variable CFC not yet in Mathlib).

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
| `Inner.lean` | Frobenius inner product `⟪A, B⟫_𝕜 = (B * Aᴴ).trace` and its properties (*done*) |
| `Jensen.lean` | Jensen's operator inequality (*sorried*) |
| `Main.lean` | `GenPerspectiveJointlyConcave` / `GenPerspectiveJointlyConvex`; `PowerMeanJointlyConcave` / `PowerMeanJointlyConvex` (*done, depending on Jensen*) |
| `MatrixSpecialization.lean` | `FrobeniusMat` namespace: all typeclasses for `Matrix n n 𝕜` with Frobenius norm/inner product — `NormedAddCommGroup`, `InnerProductSpace`, `NormedRing`, `CompleteSpace`, `HStarAlgebra`, `ContinuousFunctionalCalculus`, and their CLM endomorphism counterparts (*done*) |
| `Lieb.lean` | Abstract H\*-algebra theorems: `LiebConcavity_general`, `AndoConvexity_general`, `LiebExtension` [Thm 1.2(b)], `LiebConcavity` [Thm 1.2(a)], `AndoConvexity` [Thm 1.4] (*done*); `FrobeniusMat` namespace: matrix specializations of all three main theorems with `A.PosDef ∧ B.PosSemidef` hypotheses and explicit trace formula `re ((A ^ _ * K * B ^ _ * Kᴴ).trace)` (*done*) |
| `ForMathlib.lean` | Lemmas not yet in Mathlib: `Commute.rpow_right/left/rpow`, `mul_rpow_of_commute` (*sorried*), `cfc_isStrictlyPositive_of_pos/nonneg`, strict positivity lemmas, `spectrum_subset_convex_comb` |
| `MulOppositeStarAlgEquiv.lean` | `starAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ`; `opStar`; CFC and rpow commutativity across `op` (*done*) |

## Building

Requires a compatible Lean 4 toolchain (see `lean-toolchain`).

```bash
lake build
