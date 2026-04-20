/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Inner product space structure on `Matrix n n 𝕜`

Builds `InnerProductSpace 𝕜 (Matrix n n 𝕜)` with inner product `⟪X, Y⟫ = (Y * Xᴴ).trace`,
whose norm `‖X‖ = √(∑ᵢⱼ |Xᵢⱼ|²)` is identical with the Frobenius norm.

Following `Mathlib.Analysis.Matrix.Normed`: definitions are **not** declared as
global instances. Activate them by `open scoped Matrix.Norms.Frobenius`.
-/
@[expose] public section

open scoped InnerProductSpace Matrix
open RCLike
variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n]

namespace Matrix

/-- The Frobenius inner product `⟪A, B⟫_𝕜 = (B * Aᴴ).trace` on `Matrix n n 𝕜`. -/
@[instance_reducible]
def frobeniusInner : Inner 𝕜 (Matrix n n 𝕜) where
  inner A B := (B * Aᴴ).trace

-- Active only within this file, for the proofs below.
attribute [local instance] Matrix.frobeniusInner
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

@[simp]
theorem frobenius_inner_def (A B : Matrix n n 𝕜) :
    ⟪A, B⟫_𝕜 = (B * Aᴴ).trace :=
  rfl

noncomputable section

lemma inner_self_eq_sum_sq {A : Matrix n n 𝕜} :
    re ⟪A, A⟫_𝕜 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp_rw [frobenius_inner_def, trace, diag, mul_apply, conjTranspose_apply, map_sum]
  simp [mul_conj, sq]

theorem frobenius_norm_sq_eq_re_inner (A : Matrix n n 𝕜) :
    ‖A‖ ^ 2 = re ⟪A, A⟫_𝕜 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt, inner_self_eq_sum_sq]
  · simp
  · positivity

/-- `Matrix n n 𝕜` with the Frobenius inner product `⟪A, B⟫ = (B * Aᴴ).trace`
is an inner product space. Not a global instance;
activate via `open scoped Matrix.Norms.FrobeniusInner`. -/
@[instance_reducible]
def frobeniusInnerProductSpace : InnerProductSpace 𝕜 (Matrix n n 𝕜) where
  norm_sq_eq_re_inner := frobenius_norm_sq_eq_re_inner
  conj_inner_symm := by
    simp [starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul]
  add_left := by simp [mul_add]
  smul_left := by simp_rw [starRingEnd_apply]; simp

end -- noncomputable

/-! ### Additional instances for Matrix.Norms.Frobenius

`open scoped Matrix.Norms.Frobenius` now also activates the
Frobenius-norm-compatible `InnerProductSpace` instance. -/

namespace Norms.Frobenius

attribute [scoped instance]
  Matrix.frobeniusInner
  Matrix.frobeniusInnerProductSpace
end Norms.Frobenius

end Matrix
