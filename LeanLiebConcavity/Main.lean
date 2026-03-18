import LeanLiebConcavity.Jensen
import LeanLiebConcavity.ForMathlib

/-- now need properties of Hermitian matrices -/
example : 1 = 1 := rfl

noncomputable section

open NNReal

namespace CFC
open Set

--namespace IsSelfAdjoint
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
variable {L₁ L₂ R₁ R₂ : A}
variable {f g : ℝ → ℝ}

theorem PerspectiveJointConvex
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0)
    (hg : ContinuousOn g (Ici 0) ∧ ∀ ⦃x : ℝ⦄, 0 < x → 0 < g x)
    (h_opconvex : OperatorConvexOn (Ici 0) f)
    (hg_opconcav : OperatorConcaveOn (Ici 0) g)
    (hL : 0 ≤ L₁ ∧ 0 ≤ L₂)
    (hR₁ : IsStrictlyPositive R₁) (hR₂ : IsStrictlyPositive R₂) :
    ∀⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (GenPerspective A f g) (a • L₁ + b • L₂, a • R₁ + b • R₂)
      ≤ a • (GenPerspective A f g) (L₁, R₁) + b • (GenPerspective A f g) (L₂, R₂) := by
    intros a b ha hb hab
    rcases ha.eq_or_lt_dec with rfl | ha'
    · -- a = 0
      simp at *; simp [hab]
    rcases hb.eq_or_lt_dec with rfl | hb'
    · -- b = 0
      simp at *; simp [hab]

    simp only [GenPerspective]
    let R := a • R₁ + b • R₂
    let T₁ := (a • cfc g R₁) ^ (1/2 : ℝ) * (cfc g R) ^ (-1/2 : ℝ)
    let T₂ := (b • cfc g R₂) ^ (1/2 : ℝ) * (cfc g R) ^ (-1/2 : ℝ)
    have hT₁_star : star T₁ = (cfc g R) ^ (-1/2 : ℝ) * (a • cfc g R₁) ^ (1/2 : ℝ) := by
      grind [IsSelfAdjoint.of_nonneg, IsSelfAdjoint.star_mul_eq]
    have hT₂_star : star T₂ = (cfc g R) ^ (-1/2 : ℝ) * (b • cfc g R₂) ^ (1/2 : ℝ) := by
      grind [IsSelfAdjoint.of_nonneg, IsSelfAdjoint.star_mul_eq]
    have hR : IsStrictlyPositive R := by grind only [isStrictlyPositive_convex_combination]
    have hgR : IsStrictlyPositive (cfc g R) :=
      cfc_isStrictlyPositive_of_pos hR hg.2
      (hg.1.mono (fun x hx => spectrum_nonneg_of_nonneg hR.nonneg hx))
    have : IsStrictlyPositive (cfc g R₁) :=
      cfc_isStrictlyPositive_of_pos hR₁ hg.2
      (hg.1.mono (fun x hx => spectrum_nonneg_of_nonneg hR₁.nonneg hx))
    have hagR₁ : IsStrictlyPositive (a • cfc g R₁) :=
      IsStrictlyPositive.smul ha' this
    have : IsStrictlyPositive (cfc g R₂) :=
      cfc_isStrictlyPositive_of_pos hR₂ hg.2
      (hg.1.mono (fun x hx => spectrum_nonneg_of_nonneg hR₂.nonneg hx))
    have hbgR₂ : IsStrictlyPositive (b • cfc g R₂) :=
      IsStrictlyPositive.smul hb' this
    have : a • cfc g R₁ + b • cfc g R₂ ≤ cfc g R := sorry
    have hT : star T₁ * T₁ + star T₂ * T₂ ≤ 1 := by
      calc
        star T₁ * T₁ + star T₂ * T₂
        = (cfc g R) ^ (-1/2 : ℝ) * (a • cfc g R₁) ^ (1/2 : ℝ)
          * (a • cfc g R₁) ^ (1/2 : ℝ) * (cfc g R) ^ (-1/2 : ℝ)
          + (cfc g R) ^ (-1/2 : ℝ) * (b • cfc g R₂) ^ (1/2 : ℝ)
          * (b • cfc g R₂) ^ (1/2 : ℝ) * (cfc g R) ^ (-1/2 : ℝ) := by
            grind only
      _ = (cfc g R) ^ (-1/2 : ℝ) * (a • cfc g R₁) ^ (1/2 + 1/2 : ℝ)
          * (cfc g R) ^ (-1/2 : ℝ)
          + (cfc g R) ^ (-1/2 : ℝ) * (b • cfc g R₂) ^ (1/2 + 1/2 : ℝ)
          * (cfc g R) ^ (-1/2 : ℝ) := by
            grind only [rpow_add, hagR₁.isUnit, hbgR₂.isUnit]
      _ = (cfc g R) ^ (-1/2 : ℝ) * (a • cfc g R₁) * (cfc g R) ^ (-1/2 : ℝ)
          + (cfc g R) ^ (-1/2 : ℝ) * (b • cfc g R₂) * (cfc g R) ^ (-1/2 : ℝ) := by
            grind only [rpow_one, hagR₁.nonneg, hbgR₂.nonneg]
      _ = (cfc g R) ^ (-1/2 : ℝ) * (a • cfc g R₁ + b • cfc g R₂) * (cfc g R) ^ (-1/2 : ℝ) := by
            grind only
      _ ≤ (cfc g R) ^ (-1/2 : ℝ) * (cfc g R) * (cfc g R) ^ (-1/2 : ℝ) := by
            have : IsSelfAdjoint ((cfc g R) ^ (-1/2 : ℝ)) := IsSelfAdjoint.of_nonneg (by simp)
            grind only [this.conjugate_le_conjugate]
      _ = (cfc g R) ^ (-1/2 : ℝ) * (cfc g R) ^ (1 : ℝ) * (cfc g R) ^ (-1/2 : ℝ) := by
            simp only [rpow_one, hgR.nonneg]
      _ = (cfc g R) ^ (-1/2 + 1 + -1/2 : ℝ) := by
            simp only [rpow_add, hgR.isUnit]
      _ = (cfc g R) ^ (0 : ℝ) := by ring_nf
      _ = (1 : A) := by simp only [rpow_zero, hgR.nonneg]
    have : 1 + 2 = 3 := by norm_num
    sorry







variable (r : ℝ)
example : 0 ≤ L₁ ^ r := by simp
example : IsSelfAdjoint (cfc f L₁) := by simp
example : IsSelfAdjoint (L₁ ^ r) := IsSelfAdjoint.of_nonneg (by simp)
example : (1 / 2: ℝ) + 1 / 2 = (1 : ℝ) := add_halves 1
example {a b c d : A} : a * b * d + a * c * d= a * (b + c) * d := by grind only
example {a : A} (ha : IsUnit a) (ha' : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) * a ^ (-1 : ℝ) = 1 := by
  grind [rpow_neg_mul_rpow (-1) ha ha']
example {a : A} (ha : IsStrictlyPositive a) : IsUnit a := IsStrictlyPositive.isUnit ha

theorem PerspectiveJointConcave : 1 + 1 = 2 := by rfl


end CFC
