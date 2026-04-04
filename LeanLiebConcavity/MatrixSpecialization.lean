module

public import LeanLiebConcavity.HStarAlgebra
public import LeanLiebConcavity.Inner
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap


/-!
# Specialization to n×n Complex Matrices

This file instantiates all typeclasses required by `HStarAlgebra ℂ` on
`Matrix n n ℂ` with the Frobenius inner product
`⟪X, Y⟫ = Tr(Y * Xᴴ)` and the Loewner (PSD) partial order,
together with `CStarAlgebra` and `StarOrderedRing` instances on endomorphisms.
-/

@[expose] public section

noncomputable section

namespace FrobeniusMat
open scoped ComplexOrder Matrix

variable {n : Type*}


section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]


section underpin

variable [Fintype n]

/-! ### Norm and InnerProductSpace -/

/-- The Frobenius norm on `Matrix n n 𝕜`: `‖X‖_F = (∑ᵢⱼ |Xᵢⱼ|²)^(1/2)`.
Built on nested `PiLp 2` layers, so topology is the standard product topology, diamond avoid -/
instance (priority := high) instNormedAddCommGroup : NormedAddCommGroup (Matrix n n 𝕜) :=
  Matrix.frobeniusNormedAddCommGroup
--- example : (inferInstance : TopologicalSpace (Matrix n n 𝕜))
---     = NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace :=
---   rfl

/-- The inner product `⟪A, B⟫_𝕜 = (B * Aᴴ).trace` that is compatible with Frobenius norm. -/
instance (priority := high) instInnerProductSpace : InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  Matrix.frobeniusInnerProductSpace

variable [DecidableEq n]

/-- The Frobenius norm is good -/
instance (priority := high) instNormedRing : NormedRing (Matrix n n 𝕜) :=
  Matrix.frobeniusNormedRing

/-! ### HStarAlgebra instance -/

open Matrix in
/-- `Matrix n n ℂ` with the Frobenius inner product is an H*-algebra.

The two H*-algebra axioms follow from trace cyclicity `tr(AB) = tr(BA)`. -/
@[instance_reducible, scoped instance]
def instHStarAlgebra : HStarAlgebra 𝕜 (Matrix n n 𝕜) where
  __ := (inferInstance : NormedRing (Matrix n n 𝕜))
  __ := (inferInstance : InnerProductSpace 𝕜 (Matrix n n 𝕜))
  __ := (inferInstance : Algebra 𝕜 (Matrix n n 𝕜))
  __ := (inferInstance : StarRing (Matrix n n 𝕜))
  inner_mul_left {a x y} := by
    simp only [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose]
    rw [← mul_assoc, trace_mul_comm (y * xᴴ) aᴴ, mul_assoc]
  inner_mul_right {a x y} := by
    simp [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose, mul_assoc]

end underpin

section Order

/-! ### PartialOrder, StarOrderedRing -/

--- Loewner (PSD) partial order: `A ≤ B ↔ (B - A).PosSemidef`.
instance LoewnerOrder : PartialOrder (Matrix n n 𝕜) :=
  Matrix.instPartialOrder

variable [Fintype n]

--- Star-ordered ring on `Matrix n n 𝕜` under the Loewner order.
instance instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
   Matrix.instStarOrderedRing

/-! ### PosSMulMono ℝ (Matrix n n ℂ) -/

set_option linter.unusedFintypeInType false in
/-- Nonneg real scalar multiplication preserves the Loewner order on `Matrix n n 𝕜`. -/
instance instPosSMulMono : PosSMulMono ℝ (Matrix n n 𝕜) := IsOrderedModule.toPosSMulMono

/-! ### NonnegSpectrumClass -/
--- Nonnegativity With respect to loewner order.
instance instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) :=
  Matrix.instNonnegSpectrumClass

end Order

/-! ### ContinuousFunctionalCalculus (inferred) -/

/-!
## Instances on (continuous) linear endomorphisms

Once we setup the norm for `Matrix n n 𝕜`,
The (operator) norm on `Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜` is instantiated.
For CStarAlgebra and StarOrderRing instances, need to set 𝕜 = ℂ
-/

/-! ### NormedRing (inferred) -/

/-! ### Partial Order -/

set_option backward.isDefEq.respectTransparency false in
/-- Loewner partial order on `Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜`. -/
instance LoewnerOrderCLM [Fintype n] : PartialOrder (Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜) :=
  ContinuousLinearMap.instLoewnerPartialOrder --- `inferInstance` √

end RCLike

section Complex

/-! ### CStarAlgebra (inferred) -/

/-! ### StarOrderedRing (inferred) -/

end Complex

attribute [scoped instance] instNormedAddCommGroup instNormedRing instInnerProductSpace
LoewnerOrder instPosSMulMono instNonnegSpectrumClass instStarOrderedRing
LoewnerOrderCLM

end FrobeniusMat
