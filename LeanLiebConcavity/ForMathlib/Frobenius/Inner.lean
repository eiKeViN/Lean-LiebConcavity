module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Inner product space structure on `Matrix n n 𝕜`

Builds `InnerProductSpace 𝕜 (Matrix n n 𝕜)` with inner product `⟪X, Y⟫ = (Y * Xᴴ).trace`,
whose norm `‖X‖ = √(∑ᵢⱼ |Xᵢⱼ|²)` is identical with the Frobenius norm.
-/
@[expose] public section

open scoped InnerProductSpace Matrix
open RCLike
variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n]


section defs

instance frobenius_inner : Inner 𝕜 (Matrix n n 𝕜) where
  inner A B := (B * Aᴴ).trace

theorem frobenius_inner_def (A B : Matrix n n 𝕜) :
    ⟪A, B⟫_𝕜 = (B * Aᴴ).trace :=
  rfl

end defs

noncomputable section

namespace Matrix

attribute [scoped instance] Matrix.frobeniusNormedSpace
/-- the frobenius norm on n by n matrices-/
notation "‖" A "‖_F" => norm A

private lemma inner_self_eq_sum_sq {A : Matrix n n 𝕜} :
    re ⟪A, A⟫_𝕜 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp_rw [frobenius_inner_def, trace, diag, mul_apply, conjTranspose_apply, map_sum]
  simp [mul_conj, sq]

scoped instance : SeminormedAddCommGroup (Matrix n n 𝕜) :=
  Matrix.frobeniusSeminormedAddCommGroup

theorem frobenius_norm_sq_eq_re_inner (A : Matrix n n 𝕜) :
    ‖ A ‖_F ^ 2 = re ⟪A, A⟫_𝕜 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt, inner_self_eq_sum_sq]
  · simp
  · positivity

@[implicit_reducible]
def frobeniusInnerProductSpace :
    InnerProductSpace 𝕜 (Matrix n n 𝕜) where
  norm_sq_eq_re_inner := frobenius_norm_sq_eq_re_inner
  conj_inner_symm := by
    simp [frobenius_inner_def, starRingEnd_apply,
              ← trace_conjTranspose, conjTranspose_mul]
  add_left := by
    simp [frobenius_inner_def, mul_add]
  smul_left := by
    simp_rw [frobenius_inner_def, starRingEnd_apply]; simp

end Matrix

end
