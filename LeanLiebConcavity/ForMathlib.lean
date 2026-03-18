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
then `cfc f a` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_pos
    {f : ℝ → ℝ} {a : A}
    (ha : IsStrictlyPositive a)
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x)
    (hf_cont : ContinuousOn f (spectrum ℝ a)) :
    IsStrictlyPositive (cfc f a) := by
  have := (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha).2
  exact (cfc_isStrictlyPositive_iff f a hf_cont ha.1.isSelfAdjoint).mpr
    fun x hx => hf_pos (this x hx)

end CFC

section StrictPositivity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- TODO: upstream to IsStrictlyPositive or elsewhere?
/-- Convex combinations of strictly positive elements are strictly positive. -/
theorem isStrictlyPositive_convex_combination
    {a b : ℝ} {x y : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : IsStrictlyPositive x) (hy : IsStrictlyPositive y) :
    IsStrictlyPositive (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_smul, zero_add] at hab ⊢; rwa [hab, one_smul]
  · exact (hx.smul ha_pos).add_nonneg (smul_nonneg hb hy.nonneg)

end StrictPositivity

end
