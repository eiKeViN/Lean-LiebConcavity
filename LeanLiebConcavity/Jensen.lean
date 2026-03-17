import LeanLiebConcavity.Defs

noncomputable section

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Strong Jensen's Operator Inequality (Hansen–Pedersen 2003):

Let `A` be an ordered unital C⋆-algebra and `f : ℝ → ℝ` a continuous operator convex
function on a convex set `I`.
Suppose:
1. `a₁ a₂ : A` are self-adjoint with `spectrum ℝ aᵢ ⊆ I`.
2. `b₁ b₂ : A` satisfy `star b₁ * b₁ + star b₂ * b₂ = 1`.

Then:
`cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤ star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂`.
-/
-- [thm:jensen_2012] Li-Wu 2012, Operator Jensen's Inequality on C*-algebras
theorem JensenOperator2012
    {I : Set ℝ} (hI : Convex ℝ I)
    {f : ℝ → ℝ} (hf : ContinuousOn f I)
    (hf_opconvex : OperatorConvexOn I f)
    {a₁ a₂ : A} (ha₁ : IsSelfAdjoint a₁) (ha₂ : IsSelfAdjoint a₂)
    (ha₁_spec : spectrum ℝ a₁ ⊆ I) (ha₂_spec : spectrum ℝ a₂ ⊆ I)
    {b₁ b₂ : A} (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  sorry

theorem JensenOperator2012'
    {I : Set ℝ} (hI : Convex ℝ I ∧ 0 ∈ I)
    {f : ℝ → ℝ} (hf : ContinuousOn f I ∧ f 0 ≤ 0)
    (hf_opconvex : OperatorConvexOn I f)
    {a₁ a₂ : A} (ha₁ : IsSelfAdjoint a₁) (ha₂ : IsSelfAdjoint a₂)
    (ha₁_spec : spectrum ℝ a₁ ⊆ I) (ha₂_spec : spectrum ℝ a₂ ⊆ I)
    {b₁ b₂ : A} (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ :=
  sorry

/--
theorem JensenOperator2012_Pos
    {f : ℝ → ℝ} (hf : Continuous f ∧ f 0 = 0)
    (hf_opconvex : OperatorConvexOn I f)
    {a₁ a₂ : A} (ha₁ : IsStrictlyPositive a₁) (ha₂ : IsStrictlyPositive a₂)
    {b₁ b₂ : A} (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  sorry
-/
lemma ddd : 1 + 1 = 2 := by norm_num
end CFC

open NNReal

variable (a : ℝ≥0)
example : Continuous (fun (x : ℝ) ↦ x ^ (a : ℝ)) :=
  Real.continuous_rpow_const zero_le_coe
