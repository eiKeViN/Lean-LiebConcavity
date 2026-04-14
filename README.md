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

| File | Contents |
|------|----------|
| `LeanLiebConcavity/Defs.lean` | `OperatorConvexOn` / `OperatorConcaveOn`; `PerspectiveFunction`; `GenPerspectiveFunction`; `OperatorPowerMean`; `GenPerspective_of_commute` ✓; `GenPerspective_of_rpow_commute` ✓ |
| `LeanLiebConcavity/HStarAlgebra.lean` | H\*-algebra typeclass; `Lmul` / `Rmul` as star-algebra homs ✓; CFC commutativity `L_{f(a)} = f(L_a)` and `R_{f(a)} = f(R_a)` ✓; `Rmul_rpow_strictlyPositive` variants ✓ |
| `LeanLiebConcavity/Jensen.lean` | **Jensen's operator inequality** (Li–Wu 2012): `JensenOperator_convex_general` ✓; `JensenOperator_convex_general_sub` ✓; n=2 specializations and concave/nonneg variants ✓ |
| `LeanLiebConcavity/Main.lean` | `PerspectiveJointConvex` / `PerspectiveJointConcave` ✓; `PowerMeanJointlyConcave` / `PowerMeanJointlyConvex` ✓; `PowerOperatorConvex` / `PowerOperatorConcave` |
| `LeanLiebConcavity/Lieb.lean` | `LiebConcavity` [Thm 1.2(a)] ✓; `LiebExtension` [Thm 1.2(b)] ✓; `AndoConvexity` [Thm 1.4] ✓; matrix specializations with explicit trace formula ✓ |

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
