# Lean-LiebConcavity

A **Lean 4 / Mathlib** formalization of **Lieb's concavity theorem**, a key result in
quantum information theory, together with Lieb's extension theorem and Ando's convexity
theorem. The formalization works in full generality for any H\*-algebra (Ambrose 1945)
satisfying appropriate order axioms — a Hilbert space equipped with a compatible normed
ring structure and star operation. The motivating example is the space of n×n complex
matrices with Frobenius inner product and conjugate-transpose star.

The main theorems — `LiebConcavity` [Thm 1.2(a)], `LiebExtension` [Thm 1.2(b)], and
`AndoConvexity` [Thm 1.4] — are fully proved. The two remaining open sorries are
structural: `mul_rpow_of_commute` (requires two-variable CFC not yet in Mathlib) and the
Löwner-theorem corollaries `PowerOperatorConvex`/`PowerOperatorConcave`.

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

### Core theory

| File | Contents |
|------|----------|
| `LeanLiebConcavity/Defs.lean` | `OperatorConvexOn` / `OperatorConcaveOn`; `PerspectiveFunction`; `GenPerspectiveFunction`; `OperatorPowerMean`; `GenPerspective_of_commute` ✓; `GenPerspective_of_rpow_commute` ✓ |
| `LeanLiebConcavity/HStarAlgebra.lean` | H\*-algebra typeclass; `Lmul` / `Rmul` as star-algebra homs ✓; CFC commutativity `L_{f(a)} = f(L_a)` and `R_{f(a)} = f(R_a)` ✓; `Rmul_rpow_strictlyPositive` variants ✓ |
| `LeanLiebConcavity/Jensen.lean` | **Jensen's operator inequality** (Li–Wu 2012): `JensenOperator_convex_general` ✓; `JensenOperator_convex_general_sub` ✓; n=2 specializations and concave/nonneg variants ✓ |
| `LeanLiebConcavity/Main.lean` | `PerspectiveJointConvex` / `PerspectiveJointConcave` ✓; `PowerMeanJointlyConcave` / `PowerMeanJointlyConvex` ✓; `PowerOperatorConvex` / `PowerOperatorConcave` |
| `LeanLiebConcavity/Lieb.lean` | `LiebConcavity` [Thm 1.2(a)] ✓; `LiebExtension` [Thm 1.2(b)] ✓; `AndoConvexity` [Thm 1.4] ✓; matrix specializations with explicit trace formula ✓ |

### Jensen proof infrastructure

These files exist solely to support `Jensen.lean` and are not imported elsewhere.

| File | Contents |
|------|----------|
| `LeanLiebConcavity/ConjugateWeightedSum.lean` | Spectrum and self-adjointness of conjugate-weighted sums `∑ star(b i) * a i * b i`; `algebraMap_le_sum_conj` |

### Mathlib candidates (`ForMathlib/`)

Lemmas missing from Mathlib, organized by topic. `ForMathlib.lean` is a flat aggregator
importing all of these.

| File | Contents |
|------|----------|
| `Continuity.lean` | `rpow_continuousOn_pos` |
| `SelfAdjoint.lean` | `IsSelfAdjoint.star_mul_eq`; `isSelfAdjoint_linear_comb` |
| `CStarMatrix.lean` | Auxiliary `ofMatrix` lemmas for `CStarMatrix` |
| `InnerProductSpace/Positive.lean` | `reApplyInnerSelf_mono_right/left` |
| `Frobenius/Inner.lean` | Frobenius inner product `⟪A, B⟫_𝕜 = (B * Aᴴ).trace` and its properties |
| `Frobenius/Matrix.lean` | `NormedAddCommGroup`, `InnerProductSpace`, `NormedRing`, `HStarAlgebra`, `ContinuousFunctionalCalculus`, `PartialOrder`, `StarOrderedRing`, `NonnegSpectrumClass` instances for `Matrix n n 𝕜` with Frobenius norm |
| `ContinuousFunctionalCalculus/Unital.lean` | `nonneg_iff_sa_spectrum_nonneg` and variant |
| `ContinuousFunctionalCalculus/Order.lean` | `isUnit_of_le_general`; `isStrictlyPositive_of_le`; `isStrictlyPositive_add_nonneg` |
| `ContinuousFunctionalCalculus/Commute.lean` | `Commute.cfc_cfc`; `IsSelfAdjoint.cfc_cfc`; `Commute.cfc_cfc_real` |
| `ContinuousFunctionalCalculus/Rpow.lean` | `mul_rpow_of_commute` (ADMITTED); `Commute.rpow_right/left/rpow_rpow`; `cfc_isStrictlyPositive_of_pos/nonneg`; rpow–mul identities |
| `ContinuousFunctionalCalculus/Convex.lean` | `isStrictlyPositive_convex_comb`; `spectrum_subset_convex_comb`; convexity lemmas for self-adjoint elements |
| `StarAlgHom/Diagonal.lean` | `diagonalStarAlgHom` as a `StarAlgHom`; `cfc_diagonal`; spectrum and order facts for diagonal matrices |
| `StarAlgHom/Unitary.lean` | `CStarAlgebra.cfc_unitary_conj'` — CFC commutes with unitary conjugation |
| `StarAlgHom/OpStar.lean` | `starAlgEquiv : A ≃⋆ₐ[R] Aᵐᵒᵖ`; `opStar_map_cfc`; CFC and rpow commutativity across `MulOpposite` |

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
