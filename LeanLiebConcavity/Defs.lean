import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic


noncomputable section

namespace CFC

universe u

/-- `f : ℝ → ℝ` is *operator convex* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is convex on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConvexOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)

/-- `f : ℝ → ℝ` is *operator concave* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is concave on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConcaveOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConcaveOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
theorem operatorConvex_apply
    {f : ℝ → ℝ} {I : Set ℝ} (hf : OperatorConvexOn.{u} I f) :
    ConvexOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
  @hf A _ _ _

theorem operatorConcave_apply
    {f : ℝ → ℝ} {I : Set ℝ} (hf : OperatorConcaveOn.{u} I f) :
    ConcaveOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
  @hf A _ _ _


open Set


section positive
open NNReal
--helpful definition for operator convexity of positive elements only

def OperatorConcaveOn_pos (f : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ ⦃B : Type*⦄ [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConcaveOn ℝ {a : B | 0 ≤ a} (cfc f)

end positive


-- [def:gen_perspective] Ebadian–Nikoufar–Eshaghi Gordji 2011, generalized perspective function
-- (f △ h)(L, R) ≔ h(R)^{1/2} f(h(R)^{-1/2} L h(R)^{-1/2}) h(R)^{1/2}
/-- The *generalized perspective function* associated to `f h : ℝ → ℝ`.-/
def GenPerspective (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f g : ℝ → ℝ) : A × A → A :=
  fun (L, R) ↦
    let gR := cfc g R
    gR ^ (1/2 : ℝ) * cfc f (gR ^ (-(1/2) : ℝ) * L * gR ^ (-(1/2) : ℝ)) * gR ^ (1/2 : ℝ)

variable (f h : ℝ → ℝ)
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (L R : A)
#check (GenPerspective A f h)

end CFC

variable (a : ℝ)

example : ℝ → ℝ := fun x ↦ x ^ a
