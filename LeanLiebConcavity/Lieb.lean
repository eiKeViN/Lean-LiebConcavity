import LeanLiebConcavity.HStarAlgebra
import LeanLiebConcavity.Main
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

noncomputable section

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [HStarAlgebra ℂ H]

/-- ad-hoc ℝ in ℂ scalar multiplication lemmas -/
@[simp, grind .]
private lemma Lmul_smul_real (a : ℝ) (A : H) :
    Lmul ℂ (a • A) = a • Lmul ℂ A := by
 calc Lmul ℂ (a • A)
        = Lmul ℂ ((↑a : ℂ) • A) := by rw [Complex.coe_smul]
      _ = (↑a : ℂ) • Lmul ℂ A := by rw [Lmul_smul]
      _ = a • Lmul ℂ A := by rw [<- Complex.coe_smul]

@[simp, grind .]
private lemma Rmul_smul_real (a : ℝ) (A : H) :
    Rmul ℂ (a • A) = a • Rmul ℂ A := by
 calc Rmul ℂ (a • A)
        = Rmul ℂ ((↑a : ℂ) • A) := by rw [Complex.coe_smul]
      _ = (↑a : ℂ) • Rmul ℂ A := by rw [Rmul_smul]
      _ = a • Rmul ℂ A := by rw [<- Complex.coe_smul]

variable [CompleteSpace H] [PartialOrder H] [StarOrderedRing H]
  [ContinuousFunctionalCalculus ℝ H IsSelfAdjoint] [NonnegSpectrumClass ℝ H]
attribute [local instance] instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
attribute [local instance] ContinuousLinearMap.instLoewnerPartialOrder
variable [StarOrderedRing (H →L[ℂ] H)]

def OperatorPowerMean (α β : ℝ) (A B : H) : H →L[ℂ] H :=
  GenPerspective (H →L[ℂ] H) (· ^ α) (· ^ β) (Rmul ℂ B, Lmul ℂ A)

set_option backward.isDefEq.respectTransparency false in
theorem OperatorPowerMean_apply {α β : ℝ} {A B : H}
    (hA : IsStrictlyPositive A) (hB : 0 ≤ B) (hα : 0 ≤ α) (hβ : β ≠ 0) (x : H) :
    OperatorPowerMean α β A B x = A ^ (β * (1 - α)) * x * B ^ α := by
  simp only [OperatorPowerMean,
    GenPerspective_of_rpow_commute (Lmul_Rmul_comm ℂ).symm
      (Rmul_nonneg ℂ hB) (Lmul_isStrictlyPositive ℂ hA) hβ]
  rw [ContinuousLinearMap.mul_apply]
  -- note: this part builds slower because typeclasses for (H →L[ℂ] H)ᵐᵒᵖ are inferred by machine.
  rw [Rmul_rpow_nonneg_apply ℂ hα hB,
      Lmul_rpow_strictlyPositive_apply ℂ hA]


variable [PosSMulMono ℝ H]
theorem OperatorPowerMean_jointly_concave {α β : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) :
    ConcaveOn ℝ {p : H × H | IsStrictlyPositive p.1 ∧ 0 ≤ p.2}
      (fun (A, B) => OperatorPowerMean α β A B) := by
  refine ⟨convex_strictlyPositive_nonneg, fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  have hc := (@PowerMeanJointlyConcave (H →L[ℂ] H) _ _ _ α β hα hβ)
  simp only [OperatorPowerMean, Prod.smul_mk, Lmul_add, Rmul_add, Lmul_smul_real, Rmul_smul_real]
  exact @hc.2 ⟨Rmul ℂ B₁, Lmul ℂ A₁⟩ ⟨Rmul_nonneg ℂ h₁.2, Lmul_isStrictlyPositive ℂ h₁.1⟩
              ⟨Rmul ℂ B₂, Lmul ℂ A₂⟩ ⟨Rmul_nonneg ℂ h₂.2, Lmul_isStrictlyPositive ℂ h₂.1⟩
              a b ha hb hab

omit [CompleteSpace H] [PartialOrder H] [StarOrderedRing H]
    [ContinuousFunctionalCalculus ℝ H IsSelfAdjoint] [NonnegSpectrumClass ℝ H]
    [StarOrderedRing (H →L[ℂ] H)] [PosSMulMono ℝ H] in
/-- The map `T ↦ re ⟪T x, x⟫` is monotone w.r.t. the Loewner order.
This is the key bridge between operator inequalities and scalar inequalities. -/
lemma reApplyInnerSelf_mono {S T : H →L[ℂ] H} (h : S ≤ T) (x : H) :
    RCLike.re ⟪S x, x⟫_ℂ ≤ RCLike.re ⟪T x, x⟫_ℂ := by
  have := (ContinuousLinearMap.le_def S T).mp h |>.re_inner_nonneg_left x
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub] at this
  linarith

theorem OperatorPowerMean_jointly_convex {α β : ℝ}
    (hα : 1 ≤ α ∧ α ≤ 2) (hβ : 0 < β ∧ β ≤ 1) :
    ConvexOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => OperatorPowerMean α β A B) := by
  have hc := @PowerMeanJointlyConvex (H →L[ℂ] H) _ _ _ α β hα hβ
  refine ⟨convex_strictlyPositive_nonneg, fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  simp only [OperatorPowerMean, Prod.smul_mk, Lmul_add, Rmul_add, Lmul_smul_real, Rmul_smul_real]
  exact @hc.2 ⟨Rmul ℂ B₁, Lmul ℂ A₁⟩ ⟨Rmul_nonneg ℂ h₁.2, Lmul_isStrictlyPositive ℂ h₁.1⟩
              ⟨Rmul ℂ B₂, Lmul ℂ A₂⟩ ⟨Rmul_nonneg ℂ h₂.2, Lmul_isStrictlyPositive ℂ h₂.1⟩
              a b ha hb hab

open RCLike
/-- ## Generalised Lieb Concavity
`(A, B) ↦ re ⟪OperatorPowerMean α β A B x, x⟫` is jointly concave in `(A, B)`
for `0 < α, β ≤ 1`. -/
theorem LiebConcavity_inner {α β : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConcaveOn ℝ {p : H × H | IsStrictlyPositive p.1 ∧ 0 ≤ p.2}
      (fun (A, B) => re ⟪OperatorPowerMean α β A B x, x⟫_ℂ) := by
  refine ⟨(OperatorPowerMean_jointly_concave hα hβ).1,
          fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  have hc := (OperatorPowerMean_jointly_concave hα hβ).2
              h₁ h₂ ha hb hab
  calc a * re ⟪OperatorPowerMean α β A₁ B₁ x, x⟫_ℂ
      + b * re ⟪OperatorPowerMean α β A₂ B₂ x, x⟫_ℂ
      = re ⟪(a • OperatorPowerMean α β A₁ B₁ + b • OperatorPowerMean α β A₂ B₂) x, x⟫_ℂ := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
                     inner_add_left, map_add]
          congr 1 <;>
          · rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal]
            simp
    _ ≤ re ⟪OperatorPowerMean α β (a • A₁ + b • A₂) (a • B₁ + b • B₂) x, x⟫_ℂ :=
          reApplyInnerSelf_mono hc x

theorem LiebConcavity_inner' {α β : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConcaveOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪A ^ (β * (1 - α)) * x * B ^ α, x⟫_ℂ) := by
  refine LiebConcavity_inner hα hβ x |>.congr fun ⟨A, B⟩ ⟨hA, hB⟩ => ?_
  simp only [OperatorPowerMean_apply hA hB hα.1.le hβ.1.ne']

end
