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

- M. Nikoufar, A. Ebadian, M. Eshaghi Gordji, *Adv. Math.* **248** (2013) 531–533
- A. Ebadian, M. Nikoufar, M. Eshaghi Gordji, *PNAS* **108** (2011) 7313–7314
- F. Hansen, G. K. Pedersen, *Bull. London Math. Soc.* **35** (2003) 553–564
- F. Hansen, G. K. Pedersen, *Math. Ann.* **258** (1982) 229–241
- Y. Li, D. Wu, *J. Operator Theory* **67** (2012) 329–337

## Sorry status

| Declaration | File | Status |
|-------------|------|--------|
| `mul_rpow_of_commute` | `ForMathlib.lean` | **open** — requires two-variable CFC not in Mathlib |
| `PowerOperatorConvex` | `Main.lean` | **open** — depends on Löwner's theorem |
| `PowerOperatorConcave` | `Main.lean` | **open** — depends on Löwner's theorem |
| `JensenOperator_convex_general` | `Jensen.lean` | ✓ proved (Li–Wu 2012 Thm 2.2) |
| `JensenOperator_convex_general_sub` | `Jensen.lean` | ✓ proved (Li–Wu 2012 Cor 2.4) |
| All theorems in `Lieb.lean` | `Lieb.lean` | ✓ proved |
| All theorems in `Main.lean` except above | `Main.lean` | ✓ proved |

## Structure

### Core theory

| File | Contents |
|------|----------|
| `Defs.lean` | `OperatorConvexOn` / `OperatorConcaveOn`; `PerspectiveFunction`; `GenPerspectiveFunction`; `OperatorPowerMean`; `GenPerspective_of_commute` ✓; `GenPerspective_of_rpow_commute` ✓ (pending `mul_rpow_of_commute`) |
| `HStarAlgebra.lean` | H\*-algebra typeclass; `Lmul` / `Rmul` as star-algebra homs ✓; CFC commutativity `L_{f(a)} = f(L_a)` and `R_{f(a)} = f(R_a)` ✓; `Rmul_rpow_strictlyPositive` variants ✓ |
| `Jensen.lean` | **Jensen's operator inequality** (Li–Wu 2012): `JensenOperator_convex_general` ✓; `JensenOperator_convex_general_sub` ✓; n=2 specializations and concave/nonneg variants ✓ |
| `Main.lean` | `GenPerspectiveJointlyConcave` / `GenPerspectiveJointlyConvex` ✓; `PowerMeanJointlyConcave` / `PowerMeanJointlyConvex` ✓; `PowerOperatorConvex` / `PowerOperatorConcave` (open — Löwner) |
| `Lieb.lean` | `LiebConcavity` [Thm 1.2(a)] ✓; `LiebExtension` [Thm 1.2(b)] ✓; `AndoConvexity` [Thm 1.4] ✓; matrix specializations with explicit trace formula ✓ |

### Supporting infrastructure

| File | Contents |
|------|----------|
| `Basic.lean` | Shared imports and basic lemmas |
| `Inner.lean` | Frobenius inner product `⟪A, B⟫_𝕜 = (B * Aᴴ).trace` and its properties ✓ |
| `MatrixSpecialization.lean` | `FrobeniusMat` namespace: `NormedAddCommGroup`, `InnerProductSpace`, `NormedRing`, `CompleteSpace`, `HStarAlgebra`, `ContinuousFunctionalCalculus` instances for `Matrix n n 𝕜` with Frobenius norm ✓ |
| `MulOppositeStarAlgEquiv.lean` | `starAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ`; CFC and rpow commutativity across `MulOpposite` ✓ |
| `ForMathlib.lean` | Candidates for upstream Mathlib: `Commute.rpow_right/left`; `mul_rpow_of_commute` (open); `cfc_isStrictlyPositive_of_pos/nonneg`; `spectrum_subset_convex_comb` |

### Jensen proof infrastructure

These files exist solely to support `Jensen.lean` and are not imported elsewhere.

| File | Contents |
|------|----------|
| `ConjugateWeightedSum.lean` | Spectrum and self-adjointness of conjugate-weighted sums `∑ star(b i) * a i * b i`; `algebraMap_le_sum_conj` |
| `DiagonalStarAlgHom.lean` | `diagonalStarAlgHom` as a `StarAlgHom`; `cfc_diagonal`; spectrum and order facts for diagonal matrices in `CStarMatrix` |
| `UnitaryConjCFC.lean` | `CStarAlgebra.cfc_unitary_conj'` — CFC commutes with unitary conjugation |
| `CStarMatrixAux.lean` | Auxiliary instances for `CStarMatrix` used in the Li–Wu block-matrix construction |

## Blueprint correspondence

| Blueprint label | Lean declaration |
|-----------------|-----------------|
| `thm:jensen_1982` | (not yet formalized — HP1982 version) |
| `thm:jensen_2012` | `JensenOperator_convex_general` |
| `thm:jensen_2012'` | `JensenOperator_convex_general_sub` |
| `thm:perspective_iff_matrix_convex` | `PerspectiveIffMatrixConvex` |
| `thm:gen_perspective_jointly_convex` | `GenPerspectiveJointlyConvex` |
| `cor:gen_perspective_jointly_concave` | `GenPerspectiveJointlyConcave` |
| `thm:power_mean_jointly_concave` | `PowerMeanJointlyConcave` |
| `thm:lieb` | `LiebConcavity` |
| `thm:lieb_extension` | `LiebExtension` |
| `thm:ando_convexity` | `AndoConvexity` |

## Building

Requires a compatible Lean 4 toolchain (see `lean-toolchain`).

```bash
lake build
```
