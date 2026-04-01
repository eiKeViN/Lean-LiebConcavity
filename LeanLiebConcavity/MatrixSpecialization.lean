import LeanLiebConcavity.HStarAlgebra
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Specialization to n×n Complex Matrices

This file instantiates all typeclasses required by `HStarAlgebra ℂ` on
`Matrix n n ℂ` with the trace (Frobenius) inner product
`⟪X, Y⟫ = Tr(Y * Xᴴ)` and the Loewner (PSD) partial order.

## Step 2: NormedAddCommGroup + InnerProductSpace

We use Mathlib's `toMatrixNormedAddCommGroup` (from a positive definite matrix `M = 1`)
to equip `Matrix n n ℂ` with the norm `‖X‖ = √(Tr(Xᴴ X))`.

The inner product is `⟪X, Y⟫ = (Y * 1 * Xᴴ).trace = (Y * Xᴴ).trace`.
This is conjugate-linear in `X` and linear in `Y` (physicist convention / Mathlib convention).

Both instances are built from the same `InnerProductSpace.Core`, avoiding any norm diamond.
-/

noncomputable section

open scoped ComplexOrder Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 10000] Matrix.module

/-! ## Step 2: NormedAddCommGroup and InnerProductSpace -/

/-- The trace inner product norm on `Matrix n n ℂ`:
`‖X‖ = √(Tr(Xᴴ X))`. Built from `M = 1` via `toMatrixNormedAddCommGroup`. -/
instance instNormedAddCommGroupMatrix : NormedAddCommGroup (Matrix n n ℂ) :=
  (1 : Matrix n n ℂ).toMatrixNormedAddCommGroup Matrix.PosDef.one

attribute [local instance 10000] instNormedAddCommGroupMatrix

/-- The trace inner product `⟪X, Y⟫ = (Y * Xᴴ).trace` on `Matrix n n ℂ`,
obtained from `M = 1` in the formula `(Y * M * Xᴴ).trace`.
Consistent with `instNormedAddCommGroupMatrix` since both share the norm `√(re ⟪·,·⟫)`. -/
instance instInnerProductSpaceMatrix : InnerProductSpace ℂ (Matrix n n ℂ) :=
  letI : NormedAddCommGroup (Matrix n n ℂ) := instNormedAddCommGroupMatrix
  (1 : Matrix n n ℂ).toMatrixInnerProductSpace Matrix.PosDef.one.posSemidef

attribute [local instance 10000] instInnerProductSpaceMatrix

/-- The inner product on `Matrix n n ℂ` computes as `(Y * Xᴴ).trace`. -/
lemma inner_eq_trace (X Y : Matrix n n ℂ) :
    @inner ℂ _ instInnerProductSpaceMatrix.toInner X Y = (Y * Xᴴ).trace := by
  change (Y * 1 * Xᴴ).trace = (Y * Xᴴ).trace
  rw [mul_one]

/-! ## Step 3: NormedRing -/

omit [DecidableEq n] in
/-- The trace inner product norm equals the Frobenius norm on `Matrix n n ℂ`.
Both compute `√(∑ᵢⱼ |Aᵢⱼ|²)`, but through different definitional paths:
- trace norm: `√(re (A * Aᴴ).trace)`
- Frobenius norm: `(∑ᵢⱼ ‖Aᵢⱼ‖^2)^(1/2)` via `PiLp 2`
-- Helper: re (A * Aᴴ).trace = ∑ᵢⱼ ‖Aᵢⱼ‖² -/
private lemma trace_mul_conjTranspose_re_eq_sum_norm_sq (A : Matrix n n ℂ) :
    RCLike.re (A * Aᴴ).trace = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [map_sum]
  congr 1; ext i; congr 1; ext j
  simp [Complex.mul_conj', sq]

lemma frobenius_norm_eq_trace_norm (A : Matrix n n ℂ) :
    @norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A =
    @norm _ instNormedAddCommGroupMatrix.toNorm A := by
  symm
  change Real.sqrt (RCLike.re (@inner ℂ _ instInnerProductSpaceMatrix.toInner A A)) = _
  rw [inner_eq_trace, trace_mul_conjTranspose_re_eq_sum_norm_sq,
      Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  norm_cast

/-- `Matrix n n ℂ` is a `NormedRing` under the trace inner product norm.
`norm_mul_le` is transferred from `Matrix.frobenius_norm_mul` via `frobenius_norm_eq_trace_norm`. -/
instance instNormedRingMatrix : NormedRing (Matrix n n ℂ) where
  __ := (inferInstance : Ring (Matrix n n ℂ))
  __ := instNormedAddCommGroupMatrix
  norm_mul_le a b := by
    simpa [frobenius_norm_eq_trace_norm] using Matrix.frobenius_norm_mul a b

attribute [local instance 10000] instNormedRingMatrix
/-! ## Step 4: CompleteSpace -/

--- set_option trace.Meta.synthInstance true
--- set_option trace.Meta.isDefEq true

--- instance hello : Module ℂ (Matrix n n ℂ) := inferInstance
set_option backward.isDefEq.respectTransparency false in
instance : FiniteDimensional ℂ (Matrix n n ℂ) := inferInstance
/-- `Matrix n n ℂ` is complete: it is finite-dimensional over the complete field `ℂ`. -/
instance instCompleteSpaceMatrix : CompleteSpace (Matrix n n ℂ) := inferInstance

attribute [local instance 10000] instCompleteSpaceMatrix

/-! ## Step 5: PartialOrder, StarOrderedRing, NonnegSpectrumClass (Loewner order)

All three are scoped to `MatrixOrder`; we activate them together so each can see the others. -/

/-- Loewner (PSD) partial order: `A ≤ B ↔ (B - A).PosSemidef`. -/
instance instPartialOrderMatrix : PartialOrder (Matrix n n ℂ) := Matrix.instPartialOrder

attribute [local instance 10000] instPartialOrderMatrix

set_option backward.isDefEq.respectTransparency false in
instance instNonnegSpectrumClassMatrix : NonnegSpectrumClass ℝ (Matrix n n ℂ) :=
  Matrix.instNonnegSpectrumClass

/-- Star-ordered ring on `Matrix n n ℂ` under the Loewner order. -/
instance instStarOrderedRingMatrix : StarOrderedRing (Matrix n n ℂ) :=
  Matrix.instStarOrderedRing

/-! ## Step 6: ContinuousFunctionalCalculus -/

set_option backward.isDefEq.respectTransparency false in
/-- CFC for self-adjoint (Hermitian) matrices, independent of norm choice. -/
instance instCFCMatrix : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
  inferInstance

/-! ## Step 7: PosSMulMono ℝ (Matrix n n ℂ) -/

omit [Fintype n] in
/-- Nonneg real scalar multiplication preserves the Loewner order on `Matrix n n ℂ`.
If `A ≤ B` (i.e. `(B - A).PosSemidef`) and `0 ≤ a : ℝ`, then `a • A ≤ a • B`. -/
instance instPosSMulMonoMatrix : PosSMulMono ℝ (Matrix n n ℂ) where
  smul_le_smul_of_nonneg_left := by
    intro r hr A B hAB
    rw [Matrix.le_iff, ← Matrix.nonneg_iff_posSemidef] at hAB ⊢
    rw [← show r • (B - A) = r • B - r • A from smul_sub r B A]
    exact smul_nonneg hr hAB

/-! ## Step 8: StarOrderedRing on continuous linear endomorphisms

Note: `Matrix n n ℂ →L[ℂ] Matrix n n ℂ` here uses the product topology on `Matrix n n ℂ`,
not our trace-norm topology. On a finite-dimensional space all norms are equivalent and every
linear map is continuous, so the CLM type coincides regardless of norm choice. The instances
below are sorry'd pending a formal norm-independence argument. -/

open ContinuousLinearMap

set_option trace.Meta.synthInstance true

set_option backward.isDefEq.respectTransparency false in
instance instStarCLMMatrix : Star (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  ⟨@adjoint ℂ (Matrix n n ℂ) (Matrix n n ℂ) _ _ _ _ _ _⟩

instance instStarRingCLMMatrix : StarRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  ⟨map_add adjoint⟩

/-- Sorry'd: `CStarAlgebra` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ` (needed for CFC on CLMs). -/
instance instCStarAlgebraEndo :
    CStarAlgebra (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) := by
  haveI : NormedAddCommGroup (Matrix n n ℂ) := instNormedAddCommGroupMatrix
  haveI : InnerProductSpace ℂ (Matrix n n ℂ) := instInnerProductSpaceMatrix
  haveI : CompleteSpace (Matrix n n ℂ) := instCompleteSpaceMatrix
  haveI : StarRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) := ⟨map_add adjoint⟩

--- attribute [instance 1000] ContinuousLinearMap.instLoewnerPartialOrder

set_option backward.isDefEq.respectTransparency false in
/-- Sorry'd: `StarRing` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ` (adjoint as star).
Mathlib provides this for `[InnerProductSpace ℂ E] [CompleteSpace E]` but with the
norm-induced topology; here `Matrix n n ℂ` carries the product topology.
Sorry'd: `PartialOrder` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ` (Loewner order). -/
instance instPartialOrderCLMMatrix : PartialOrder (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) where
  le f g :=
    @(g - f).IsPositive ℂ (Matrix n n ℂ) _ instNormedAddCommGroupMatrix instInnerProductSpaceMatrix
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simpa using h₁.add h₂
  le_antisymm _ _ h₁ h₂ := coe_inj.mp (le_antisymm h₁.toLinearMap h₂.toLinearMap)

instance instStarRingCLMMatrix : StarRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
  @instCStarAlgebraEndo.toStarRing

set_option backward.isDefEq.respectTransparency false in
/-- Sorry'd: `StarOrderedRing` on `Matrix n n ℂ →L[ℂ] Matrix n n ℂ`. -/
instance instStarOrderedRingCLMMatrix [StarRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ)] :
  StarOrderedRing (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) := by
  haveI : PartialOrder (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) := inferInstance
  infer_instance

/-! ## Step 9: HStarAlgebra instance -/

open Matrix in
/-- `Matrix n n ℂ` with the trace inner product is an H*-algebra.

The two H*-algebra axioms follow from trace cyclicity `tr(AB) = tr(BA)`:
- `inner_mul_left`: `⟪a*x, y⟫ = tr(y*(ax)ᴴ) = tr(y*xᴴ*aᴴ) = tr(aᴴ*y*xᴴ) = ⟪x, aᴴ*y⟫`
- `inner_mul_right`: `⟪x*a, y⟫ = tr(y*(xa)ᴴ) = tr(y*aᴴ*xᴴ) = ⟪x, y*aᴴ⟫` -/
instance instHStarAlgebraMatrix : HStarAlgebra ℂ (Matrix n n ℂ) where
  __ := instNormedRingMatrix
  __ := instInnerProductSpaceMatrix
  __ := (inferInstance : Algebra ℂ (Matrix n n ℂ))
  __ := (inferInstance : StarRing (Matrix n n ℂ))
  inner_mul_left {a x y} := by
    simp only [inner_eq_trace, conjTranspose_mul, star_eq_conjTranspose]
    rw [← mul_assoc, trace_mul_comm (y * xᴴ) aᴴ, mul_assoc]
  inner_mul_right {a x y} := by
    simp [inner_eq_trace, conjTranspose_mul, star_eq_conjTranspose, mul_assoc]

end
