module

public import LeanLiebConcavity.HStarAlgebra
public import LeanLiebConcavity.Inner
--- import Mathlib.Analysis.Matrix.Normed
--- import Mathlib.Analysis.Matrix.Order
--- public import Mathlib.Analysis.InnerProductSpace.ofNorm
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

set_option linter.unusedDecidableInType false

open scoped ComplexOrder Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace FrobeniusMat

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### NormedAddCommGroup and InnerProductSpace -/

/-- The Frobenius norm on `Matrix n n 𝕜`: `‖X‖ = (∑ᵢⱼ |Xᵢⱼ|²)^(1/2)`.
Built on nested `PiLp 2` layers, so topology is the standard product topology, diamond avoid -/
scoped instance instNormedAddCommGroup : NormedAddCommGroup (Matrix n n 𝕜) :=
  Matrix.frobeniusNormedAddCommGroup
--- example : (inferInstance : TopologicalSpace (Matrix n n 𝕜))
---     = NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace :=
---   rfl

/-- The Frobenius inner product on `Matrix n n 𝕜`: `‖X‖ = (∑ᵢⱼ |Xᵢⱼ|²)^(1/2)`. -/
scoped instance instInnerProductSpace : InnerProductSpace 𝕜 (Matrix n n 𝕜) :=
  Matrix.frobeniusInnerProductSpace

/-! ### Normed -/

/-- The Frobenius norm is good. -/
scoped instance instNormedRing : NormedRing (Matrix n n 𝕜) :=
  Matrix.frobeniusNormedRing

scoped instance instNormedSpace : NormedSpace 𝕜 (Matrix n n 𝕜) :=
  Matrix.frobeniusNormedSpace

/-! ### CompleteSpace
Since the topology induced by (Frobenius) norm is definitionally equal to the standard one,
this creates no diamonds when used by CStarAlgebra inference.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The standard topology on `Matrix n n 𝕜` is complete. -/
scoped instance instCompleteSpace : CompleteSpace (Matrix n n 𝕜) :=
  inferInstance

/-! ### HStarAlgebra instance -/

open Matrix in
/-- `Matrix n n ℂ` with the Frobenius inner product is an H*-algebra.

The two H*-algebra axioms follow from trace cyclicity `tr(AB) = tr(BA)`:
- `inner_mul_left`: `⟪a*x, y⟫ = tr(y*(ax)ᴴ) = tr(y*xᴴ*aᴴ) = tr(aᴴ*y*xᴴ) = ⟪x, aᴴ*y⟫`
- `inner_mul_right`: `⟪x*a, y⟫ = tr(y*(xa)ᴴ) = tr(y*aᴴ*xᴴ) = ⟪x, y*aᴴ⟫` -/
@[reducible] scoped instance instHStarAlgebra : HStarAlgebra 𝕜 (Matrix n n 𝕜) where
  __ := (inferInstance : NormedRing (Matrix n n 𝕜))
  __ := (inferInstance : InnerProductSpace 𝕜 (Matrix n n 𝕜))
  __ := (inferInstance : Algebra 𝕜 (Matrix n n 𝕜))
  __ := (inferInstance : StarRing (Matrix n n 𝕜))
  inner_mul_left {a x y} := by
    simp only [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose]
    rw [← mul_assoc, trace_mul_comm (y * xᴴ) aᴴ, mul_assoc]
  inner_mul_right {a x y} := by
    simp [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose, mul_assoc]

/-! ### PartialOrder, StarOrderedRing, NonnegSpectrumClass -/

--- Loewner (PSD) partial order: `A ≤ B ↔ (B - A).PosSemidef`.
scoped instance LoewnerOrder : PartialOrder (Matrix n n 𝕜) :=
  Matrix.instPartialOrder

--- Nonnegativity With respect to loewner order.
scoped instance instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) :=
  Matrix.instNonnegSpectrumClass

--- Star-ordered ring on `Matrix n n 𝕜` under the Loewner order.
scoped instance instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
   Matrix.instStarOrderedRing

/-! ### PosSMulMono ℝ (Matrix n n ℂ) -/

/-- Nonneg real scalar multiplication preserves the Loewner order on `Matrix n n 𝕜`. -/
scoped instance instPosSMulMono : PosSMulMono ℝ (Matrix n n 𝕜) where
  smul_le_smul_of_nonneg_left := by
    intro r hr A B hAB
    rw [Matrix.le_iff, ← Matrix.nonneg_iff_posSemidef] at hAB ⊢
    rw [← show r • (B - A) = r • B - r • A from smul_sub r B A]
    exact smul_nonneg hr hAB

/-! ### ContinuousFunctionalCalculus -/

set_option backward.isDefEq.respectTransparency false in
/-- CFC for self-adjoint (Hermitian) matrices, independent of norm choice. -/
scoped instance instCFCReal : ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint :=
  inferInstance

/-!
## Instances on (continuous) linear endomorphisms

Once we setup the norm for `Matrix n n 𝕜`,
The (operator) norm on `Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜` is instantiated.
For CStarAlgebra and StarOrderRing instances, need to set 𝕜 = ℂ
-/

/-! ### NormedRing -/

set_option backward.isDefEq.respectTransparency false in
scoped instance instNormedRingCLM : NormedRing (Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜) :=
  ContinuousLinearMap.toNormedRing --- `inferInstance` √
-- example : (inferInstance : Norm (Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜)) =
--     NormedRing.toNorm :=
--   rfl

/-! ### Partial Order -/

set_option backward.isDefEq.respectTransparency false in
/-- Loewner partial order on `Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜`. -/
scoped instance LoewnerOrderCLM : PartialOrder (Matrix n n 𝕜 →L[𝕜] Matrix n n 𝕜) :=
  ContinuousLinearMap.instLoewnerPartialOrder --- `inferInstance` √

end RCLike

section Complex

/-! ### CStarAlgebra -/

set_option backward.isDefEq.respectTransparency false in
/-- `CStarAlgebra` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ`. -/
scoped instance instCStarAlgebraCLM : CStarAlgebra (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace --- `inferInstance` √

/-! ### StarOrderedRing -/

set_option backward.isDefEq.respectTransparency false in
/-- `StarOrderedRing` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ` w.r.t Loewner order -/
scoped instance instCStarRingCLM : StarOrderedRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  ContinuousLinearMap.instStarOrderedRing

end Complex

end FrobeniusMat
