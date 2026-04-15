/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import LeanLiebConcavity.HStarAlgebra
public import LeanLiebConcavity.ForMathlib.Frobenius.Inner

/-!
# Specialization to n×n Complex Matrices

This file instantiates all typeclasses required by `HStarAlgebra ℂ` instance on
`Matrix n n ℂ` endowed with the Frobenius inner product `⟪X, Y⟫ = Tr(Y * Xᴴ)`
and the Loewner (PSD) partial order.
Together `CStarAlgebra` and `StarOrderedRing` instances on continuous endomorphisms.

These are scoped instances registered in `FrobeniusMat` namespace,
the caller need to activate them by `open FrobeniusMat`.
-/

@[expose] public section

namespace FrobeniusMat

/-! ## Norm, Inner product, CFC-necessities -/
attribute [scoped instance]
  Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra
  Matrix.frobeniusIsBoundedSMul
  Matrix.frobeniusNormSMulClass
  Matrix.frobeniusInnerProductSpace
  Matrix.instPartialOrder
  Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass
  -- Nonneg real scalar multiplication preserves the Loewner order
  IsOrderedModule.toPosSMulMono
  ContinuousLinearMap.instLoewnerPartialOrder

/-!
## Instances on continuous linear endomorphisms

Once we setup the norm for `Matrix n n 𝕜`,
The (operator) norm on `Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜` is instantiated.
For CStarAlgebra and StarOrderRing instances, need 𝕜 = ℂ
- CStaralgebra needs import `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`,
- StarOrderedRing needs import `Mathlib.Analysis.InnerProductSpace.StarOrder`.
-/

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open Matrix in
/-- `Matrix n n 𝕜` with the Frobenius inner product is an H*-algebra.

The two H*-algebra axioms follow from trace cyclicity `tr(AB) = tr(BA)`. -/
@[implicit_reducible, scoped instance]
noncomputable def instHStarAlgebra : HStarAlgebra 𝕜 (Matrix n n 𝕜) where
  __ := (inferInstance : NormedRing (Matrix n n 𝕜))
  __ := (inferInstance : InnerProductSpace 𝕜 (Matrix n n 𝕜))
  __ := (inferInstance : Algebra 𝕜 (Matrix n n 𝕜))
  __ := (inferInstance : StarRing (Matrix n n 𝕜))
  inner_mul_left {a x y} := by
    simp only [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose]
    rw [← mul_assoc, trace_mul_comm (y * xᴴ) aᴴ, mul_assoc]
  inner_mul_right {a x y} := by
    simp [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose, mul_assoc]

end FrobeniusMat
