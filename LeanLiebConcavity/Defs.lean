import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Function


noncomputable section

namespace CFC

/-- `f : ℝ → ℝ` is *operator convex* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is convex on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConvexOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)

/-- `f : ℝ → ℝ` is *operator concave* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is concave on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConcaveOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConcaveOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)

end CFC

variable (a : ℝ)

example : ℝ → ℝ := fun x ↦ x ^ a
