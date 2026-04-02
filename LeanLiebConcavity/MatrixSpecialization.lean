module

public import LeanLiebConcavity.HStarAlgebra
public import LeanLiebConcavity.Inner
--- import Mathlib.Analysis.Matrix.Normed
--- import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.ofNorm
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Specialization to n×n Complex Matrices

This file instantiates all typeclasses required by `HStarAlgebra ℂ` on
`Matrix n n ℂ` with the Frobenius inner product
`⟪X, Y⟫ = Tr(Y * Xᴴ)` and the Loewner (PSD) partial order.

## Step 2: NormedAddCommGroup + InnerProductSpace

We use `Matrix.frobeniusNormedAddCommGroup` as the base `NormedAddCommGroup`.
The inner product `⟪X, Y⟫ = (Y * Xᴴ).trace` is built via `InnerProductSpace.ofNorm`:
the Frobenius norm satisfies the parallelogram identity (proved entry-by-entry using
the standard parallelogram law on `ℂ`), so the Fréchet–von Neumann–Jordan theorem gives
a compatible inner product.

## Step 8: CLM instances (sorry'd)

`Matrix n n ℂ →L[ℂ] Matrix n n ℂ` uses `instTopologicalSpaceMatrix` (Pi topology
from `Topology/Instances/Matrix.lean:49`) rather than the Frobenius-norm topology.
These are homeomorphic (all norms on finite-dimensional spaces are equivalent) but
not definitionally equal, so Mathlib's `CStarAlgebra (E →L[ℂ] E)` and
`instLoewnerPartialOrder` instances do not unify. CLM instances are sorry'd pending
a formal topology-equivalence argument.
-/

noncomputable section

open scoped ComplexOrder Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


attribute [local instance 10000] Matrix.module

set_option trace.Meta.isDefEq true
set_option trace.Meta.synthInstance true

instance (priority := 10000) : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.FrobeniusInnerProductSpace
--- example : (inferInstance : InnerProductSpace ℂ (Matrix n n ℂ))
---     = Matrix.FrobeniusInnerProductSpace :=
---   rfl

local instance : SeminormedAddCommGroup (Matrix n n ℂ) := inferInstance
--- example : (inferInstance : SeminormedAddCommGroup (Matrix n n ℂ))
---     = Matrix.frobeniusSeminormedAddCommGroup :=
---   rfl

/-! ## Step 2: NormedAddCommGroup and InnerProductSpace -/

/-- The Frobenius norm on `Matrix n n ℂ`: `‖X‖ = (∑ᵢⱼ |Xᵢⱼ|²)^(1/2)`.
Built on nested `PiLp 2` layers; topology is the standard product topology. -/
instance (priority := 10000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.frobeniusNormedAddCommGroup
--- example : (inferInstance : TopologicalSpace (Matrix n n ℂ))
---     = NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace :=
---   rfl


/-! ## Step 3: NormedRing -/

instance (priority := 10000) : NormedRing (Matrix n n ℂ) :=
  Matrix.frobeniusNormedRing

/-! ## Step 4: CompleteSpace -/

set_option backward.isDefEq.respectTransparency false in
/-- `Matrix n n ℂ` is complete: the normed space instance on Matrix n n ℂ
imported from LeanLiebConcavity.Inner (i.e. Matrix.frobeniusNormedSpace)
makes it complete. -/
instance : CompleteSpace (Matrix n n ℂ) := inferInstance
--- example : (inferInstance : NormedSpace ℂ (Matrix n n ℂ))
---    = Matrix.frobeniusNormedSpace :=
---  rfl

/-! ## Step 5: PartialOrder, StarOrderedRing, NonnegSpectrumClass (Loewner order) -/

-- Loewner (PSD) partial order: `A ≤ B ↔ (B - A).PosSemidef`.
instance (priority := 10000) : PartialOrder (Matrix n n ℂ) :=
  Matrix.instPartialOrder

instance (priority := 10000) : NonnegSpectrumClass ℝ (Matrix n n ℂ) :=
  Matrix.instNonnegSpectrumClass

/-- Star-ordered ring on `Matrix n n ℂ` under the Loewner order. -/
instance (priority := 10000) : StarOrderedRing (Matrix n n ℂ) :=
  Matrix.instStarOrderedRing

/-! ## Step 6: ContinuousFunctionalCalculus -/

set_option backward.isDefEq.respectTransparency false in
/-- CFC for self-adjoint (Hermitian) matrices, independent of norm choice. -/
instance (priority := 10000) : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
  inferInstance

/-! ## Step 7: PosSMulMono ℝ (Matrix n n ℂ) -/

omit [Fintype n] in
/-- Nonneg real scalar multiplication preserves the Loewner order on `Matrix n n ℂ`. -/
instance instPosSMulMonoMatrix : PosSMulMono ℝ (Matrix n n ℂ) where
  smul_le_smul_of_nonneg_left := by
    intro r hr A B hAB
    rw [Matrix.le_iff, ← Matrix.nonneg_iff_posSemidef] at hAB ⊢
    rw [← show r • (B - A) = r • B - r • A from smul_sub r B A]
    exact smul_nonneg hr hAB

set_option backward.isDefEq.respectTransparency false in
instance instStarCLM : NormedRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) := inferInstance

/-! ## Step 8: StarOrderedRing on continuous linear endomorphisms -/

set_option backward.isDefEq.respectTransparency false in
/-- `CStarAlgebra` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ`. -/
instance instCStarAlgebraEndo :
    CStarAlgebra (Matrix n n (α := ℂ) →L[ℂ] Matrix n n (α := ℂ)) :=
  inferInstance


/-- Sorry'd: `StarRing` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ`. -/
instance instStarRingCLMMatrix : StarRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) := inferInstance


set_option backward.isDefEq.respectTransparency false in
/-- `PartialOrder` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ` (Loewner order). -/
instance instPartialOrderCLMMatrix : PartialOrder (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  ContinuousLinearMap.instLoewnerPartialOrder

set_option backward.isDefEq.respectTransparency false in
/-- Sorry'd: `StarOrderedRing` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ`;
waiting for Mathlib to have this instance. -/
instance instStarOrderedRingCLMMatrix : StarOrderedRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  sorry


/-! ## Step 9: HStarAlgebra instance -/

open Matrix in
/-- `Matrix n n ℂ` with the Frobenius inner product is an H*-algebra.

The two H*-algebra axioms follow from trace cyclicity `tr(AB) = tr(BA)`:
- `inner_mul_left`: `⟪a*x, y⟫ = tr(y*(ax)ᴴ) = tr(y*xᴴ*aᴴ) = tr(aᴴ*y*xᴴ) = ⟪x, aᴴ*y⟫`
- `inner_mul_right`: `⟪x*a, y⟫ = tr(y*(xa)ᴴ) = tr(y*aᴴ*xᴴ) = ⟪x, y*aᴴ⟫` -/
instance instHStarAlgebraMatrix : HStarAlgebra ℂ (Matrix n n ℂ) where
  __ := (inferInstance : NormedRing (Matrix n n ℂ))
  __ := (inferInstance : InnerProductSpace ℂ (Matrix n n ℂ))
  __ := (inferInstance : Algebra ℂ (Matrix n n ℂ))
  __ := (inferInstance : StarRing (Matrix n n ℂ))
  inner_mul_left {a x y} := by
    simp only [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose]
    rw [← mul_assoc, trace_mul_comm (y * xᴴ) aᴴ, mul_assoc]
  inner_mul_right {a x y} := by
    simp [frobenius_inner_def, conjTranspose_mul, star_eq_conjTranspose, mul_assoc]

end
