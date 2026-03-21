import LeanLiebConcavity.Defs

noncomputable section


namespace CFC

universe u
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {a₁ a₂ b₁ b₂ : A}
variable {f : ℝ → ℝ} {I : Set ℝ}

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
theorem JensenOperator2012_convex
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  sorry

theorem JensenOperator2012_convex'
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ :=
  sorry


  theorem JensenOperator2012_concave
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconcave : OperatorConcaveOn I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  sorry



theorem JensenOperator2012_concave'
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) :=
  sorry

open NNReal
open Set

/-- A version of the theorem applies to positive elements of the C* algebra,
which is useful for our application.
A positive element is always self-adjoint. -/
theorem JensenOperator2012_convex_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ :=
  JensenOperator2012_convex'
    ⟨convex_Ici 0, Set.self_mem_Ici⟩
    hf hf_opconvex
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb

theorem JensenOperator2012_concave_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
    sorry
/-
theorem JensenOperator2012_nonneg_noStar
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) (hb_pos : 0 ≤ b₁ ∧ 0 ≤ b₂) :
    cfc f (b₁ * a₁ * b₁ + b₂ * a₂ * b₂) ≤
      b₁ * cfc f a₁ * b₁ + b₂ * cfc f a₂ * b₂ := by
  have hb₁_star : star b₁ = b₁ := IsSelfAdjoint.of_nonneg hb_pos.1
  have hb₂_star : star b₂ = b₂ := IsSelfAdjoint.of_nonneg hb_pos.2
  suffices h :
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂
    by simpa [hb₁_star, hb₂_star] using h
  exact JensenOperator2012_convex_nonneg hf hf_opconvex ha hb
    -/

end CFC

open NNReal

variable (a : ℝ≥0)
example : Continuous (fun (x : ℝ) ↦ x ^ (a : ℝ)) :=
  Real.continuous_rpow_const zero_le_coe
