import LeanLiebConcavity.HStarAlgebra
import LeanLiebConcavity.Main
--- import LeanLiebConcavity.MatrixSpecialization
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
variable [StarOrderedRing (H →L[ℂ] H)]

def PowerMean (α β : ℝ) (A B : H) : H →L[ℂ] H :=
  GenPerspective (H →L[ℂ] H) (· ^ α) (· ^ β) (Rmul ℂ B, Lmul ℂ A)

set_option backward.isDefEq.respectTransparency false in
theorem PowerMean_apply {α β : ℝ} {A B : H}
    (hA : IsStrictlyPositive A) (hB : 0 ≤ B) (hα : 0 ≤ α) (hβ : β ≠ 0) (x : H) :
    PowerMean α β A B x = A ^ (β * (1 - α)) * x * B ^ α := by
  simp only [PowerMean,
    GenPerspective_of_rpow_commute (Lmul_Rmul_comm ℂ).symm
      (Rmul_nonneg ℂ hB) (Lmul_isStrictlyPositive ℂ hA) hβ]
  rw [ContinuousLinearMap.mul_apply]
  -- note: this part builds slower because typeclasses for (H →L[ℂ] H)ᵐᵒᵖ are inferred by machine.
  rw [Rmul_rpow_nonneg_apply ℂ hα hB,
      Lmul_rpow_strictlyPositive_apply ℂ hA]


variable [PosSMulMono ℝ H]

theorem PowerMean_jointly_concave {α β : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) :
    ConcaveOn ℝ {p : H × H | IsStrictlyPositive p.1 ∧ 0 ≤ p.2}
      (fun (A, B) => PowerMean α β A B) := by
  refine ⟨convex_strictlyPositive_nonneg, fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  have hc := (@PowerMeanJointlyConcave (H →L[ℂ] H) _ _ _ α β hα hβ)
  simp only [PowerMean, Prod.smul_mk, Lmul_add, Rmul_add, Lmul_smul_real, Rmul_smul_real]
  exact @hc.2 ⟨Rmul ℂ B₁, Lmul ℂ A₁⟩ ⟨Rmul_nonneg ℂ h₁.2, Lmul_isStrictlyPositive ℂ h₁.1⟩
              ⟨Rmul ℂ B₂, Lmul ℂ A₂⟩ ⟨Rmul_nonneg ℂ h₂.2, Lmul_isStrictlyPositive ℂ h₂.1⟩
              a b ha hb hab

theorem PowerMean_jointly_convex {α β : ℝ}
    (hα : 1 ≤ α ∧ α ≤ 2) (hβ : 0 < β ∧ β ≤ 1) :
    ConvexOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => PowerMean α β A B) := by
  have hc := @PowerMeanJointlyConvex (H →L[ℂ] H) _ _ _ α β hα hβ
  refine ⟨convex_strictlyPositive_nonneg, fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  simp only [PowerMean, Prod.smul_mk, Lmul_add, Rmul_add, Lmul_smul_real, Rmul_smul_real]
  exact @hc.2 ⟨Rmul ℂ B₁, Lmul ℂ A₁⟩ ⟨Rmul_nonneg ℂ h₁.2, Lmul_isStrictlyPositive ℂ h₁.1⟩
              ⟨Rmul ℂ B₂, Lmul ℂ A₂⟩ ⟨Rmul_nonneg ℂ h₂.2, Lmul_isStrictlyPositive ℂ h₂.1⟩
              a b ha hb hab

open RCLike
/-- ## Generalised Lieb Concavity
`(A, B) ↦ re ⟪x, PowerMean α β A B x⟫` is jointly concave in `(A, B)`
for `0 < α, β ≤ 1`, `A` strictly positive and `B` non-negative -/
theorem LiebConcavity_general' {α β : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConcaveOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, PowerMean α β A B x⟫_ℂ) := by
  refine ⟨(PowerMean_jointly_concave hα hβ).1,
        fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  calc a * re ⟪x, PowerMean α β A₁ B₁ x⟫_ℂ
      + b * re ⟪x, PowerMean α β A₂ B₂ x⟫_ℂ
      = re ⟪x, (a • PowerMean α β A₁ B₁ + b • PowerMean α β A₂ B₂) x⟫_ℂ := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
                     inner_add_right, map_add]
          congr 1 <;>
          · rw [← Complex.coe_smul, inner_smul_right]
            simp
    _ ≤ re ⟪x, PowerMean α β (a • A₁ + b • A₂) (a • B₁ + b • B₂) x⟫_ℂ :=
          reApplyInnerSelf_mono_right ((PowerMean_jointly_concave hα hβ).2 h₁ h₂ ha hb hab) x

/-- With the explicit formula:
`(A, B) ↦ re ⟪x, A ^ (β * (1 - α)) * x * B ^ α⟫` is jointly concave -/
theorem LiebConcavity_general {α β : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConcaveOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, A ^ (β * (1 - α)) * x * B ^ α⟫_ℂ) := by
  refine LiebConcavity_general' hα hβ x |>.congr fun ⟨A, B⟩ ⟨hA, hB⟩ => ?_
  simp only [PowerMean_apply hA hB hα.1.le hβ.1.ne']


/-! ### Special cases -/

-- arithmetic facts used in the parameter correspondences below.
private lemma lieb_param_aux {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) :
    (0 < p) ∧ (p ≤ 1) ∧ (0 < q / (1 - p)) ∧ (q / (1 - p) ≤ 1) ∧
    (q / (1 - p) * (1 - p) = q) :=
  ⟨hp, by linarith, div_pos hq (by linarith),
         (div_le_one (by linarith)).mpr (by linarith),
         div_mul_cancel₀ q (by linarith)⟩

/-- **Lieb's Extension Theorem** [Nik2013, Thm 1.2(b)]:
`(A, B) ↦ re ⟪x, A ^ q * x * B ^ p⟫` is jointly concave in `(A, B)`
for `p, q > 0` with `p + q ≤ 1`, `A` strictly positive and `B` nonnegative -/
theorem LiebExtension {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) (x : H) :
    ConcaveOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, A ^ q * x * B ^ p⟫_ℂ) := by
  obtain ⟨hα₁, hα₂, hβ₁, hβ₂, hexp⟩ := lieb_param_aux hp hq hpq
  simpa only [hexp] using LiebConcavity_general ⟨hα₁, hα₂⟩ ⟨hβ₁, hβ₂⟩ x

/-- **Lieb's Concavity Theorem** [Nik2013, Thm 1.2(a)]:
Special case of `LiebExtension` with `p = 1 - s`, `q = s`. -/
theorem LiebConcavity {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : H) :
    ConcaveOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, A ^ s * x * B ^ (1 - s)⟫_ℂ) :=
  LiebExtension (by linarith) hs0 (by linarith) x

/-- ## Generalised Ando Convexity
`(A, B) ↦ re ⟪x, PowerMean α β A B x⟫` is jointly convex in `(A, B)`
for `1 ≤ α ≤ 2`, `0 < β ≤ 1`, `A` strictly positive and `B` nonneg -/
theorem AndoConvexity_general' {α β : ℝ} (hα : 1 ≤ α ∧ α ≤ 2) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConvexOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, PowerMean α β A B x⟫_ℂ) := by
  refine ⟨(PowerMean_jointly_convex hα hβ).1,
        fun ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ a b ha hb hab => ?_⟩
  calc re ⟪x, PowerMean α β (a • A₁ + b • A₂) (a • B₁ + b • B₂) x⟫_ℂ
      ≤ re ⟪x, (a • PowerMean α β A₁ B₁ + b • PowerMean α β A₂ B₂) x⟫_ℂ :=
          reApplyInnerSelf_mono_right ((PowerMean_jointly_convex hα hβ).2 h₁ h₂ ha hb hab) x
    _ = a * re ⟪x, PowerMean α β A₁ B₁ x⟫_ℂ
      + b * re ⟪x, PowerMean α β A₂ B₂ x⟫_ℂ := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
                     inner_add_right, map_add]
          congr 1 <;>
          · rw [← Complex.coe_smul, inner_smul_right]
            simp

/-- With the explicit formula:
`(A, B) ↦ re ⟪x, A ^ (β * (1 - α)) * x * B ^ α⟫` is jointly convex
for `1 ≤ α ≤ 2`, `0 < β ≤ 1`, `A` strictly positive and `B` nonneg -/
theorem AndoConvexity_general {α β : ℝ} (hα : 1 ≤ α ∧ α ≤ 2) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConvexOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, A ^ (β * (1 - α)) * x * B ^ α⟫_ℂ) := by
  refine (AndoConvexity_general' hα hβ x).congr fun ⟨A, B⟩ ⟨hA, hB⟩ => ?_
  simp only [PowerMean_apply hA hB (by linarith [hα.1] : (0 : ℝ) ≤ α) hβ.1.ne']

-- Arithmetic for Ando's parameter correspondence:
private lemma ando_param_aux {q r : ℝ} (hq : 1 ≤ q ∧ q ≤ 2) (hr : 0 < r)
    (hqr : q - r > 1) :
    (1 ≤ q) ∧ (q ≤ 2) ∧ (0 < r / (q - 1)) ∧ (r / (q - 1) ≤ 1) ∧
    (r / (q - 1) * (1 - q) = -r) := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith [hq.1]
  refine ⟨hq.1, hq.2, div_pos hr hq1, (div_le_one hq1).mpr (by linarith), ?_⟩
  field_simp; ring

/-- **Ando's Convexity Theorem** [Nik2013, Thm 1.4]:
`(A, B) ↦ re ⟪x, A ^ (-r) * x * B ^ q⟫` is jointly convex
for `1 ≤ q ≤ 2`, `0 < r`, `q - r > 1`, `A` strictly positive and `B` nonneg. -/
theorem AndoConvexity {q r : ℝ} (hq : 1 ≤ q ∧ q ≤ 2) (hr : 0 < r)
    (hqr : q - r > 1) (x : H) :
    ConvexOn ℝ {(A, B) : H × H | IsStrictlyPositive A ∧ 0 ≤ B}
      (fun (A, B) => re ⟪x, A ^ (-r) * x * B ^ q⟫_ℂ) := by
  -- α = q, β = r/(q-1): AndoConvexity_general gives A^{β*(1-α)} * x * B^α = A^{-r} * x * B^q
  obtain ⟨hα₁, hα₂, hβ₁, hβ₂, hexp⟩ := ando_param_aux hq hr hqr
  simpa only [hexp] using AndoConvexity_general ⟨hα₁, hα₂⟩ ⟨hβ₁, hβ₂⟩ x

end

/-! ## Specialization to n×n Complex Matrices

The specialized matrix theorems follow from instantiating the abstract theorems with the
`HStarAlgebra ℂ (Matrix n n ℂ)` instance from `MatrixSpecialization.lean`. They are defined
by importing `MatrixSpecialization` and calling the abstract `LiebConcavity`,
`LiebExtension`, and `AndoConvexity` theorems with the matrix instances.
(Explicit definitions omitted due to Lean 4 subscript notation parsing issues.) -/
