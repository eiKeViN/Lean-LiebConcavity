import LeanLiebConcavity.Defs

/-!
# Candidates for upstream contribution.
-/

-- TODO: ? upstream to Mathlib.Algebra.Star.SelfAdjoint
namespace IsSelfAdjoint

variable {A : Type*} [Mul A] [StarMul A]

/-- If `a` and `b` are self-adjoint, then `star (a * b) = b * a`. -/
lemma star_mul_eq {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    star (a * b) = b * a := by
  grind [star_mul, IsSelfAdjoint.star_eq]

end IsSelfAdjoint

-- TODO: ? upstream to Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
noncomputable section

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `a` is strictly positive and `f` is continuous and maps positive reals to positive reals,
then `cfc f a` is strictly positive.


Proof sketch: `IsStrictlyPositive a` gives `∀ x ∈ spectrum ℝ a, 0 < x` (via
`CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos`), hence
`∀ x ∈ spectrum ℝ a, 0 < f x`, and `cfc_isStrictlyPositive_iff` concludes. -/
theorem cfc_isStrictlyPositive_of_pos
    {f : ℝ → ℝ} {a : A}
    (ha : IsStrictlyPositive a)
    (hf_pos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hf_cont : ContinuousOn f (spectrum ℝ a)) :
    IsStrictlyPositive (cfc f a) := by
  sorry

end CFC

end
