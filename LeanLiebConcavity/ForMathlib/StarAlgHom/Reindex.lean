/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# `Matrix.reindex` as a star algebra equivalence

`Matrix.reindex e e` is a ring equivalence, but Mathlib does not bundle it as a
`StarAlgEquiv`. This file provides that upgrade.

## Main declarations

- `Matrix.reindexStarAlgEquiv`: `Matrix.reindex e e` as a `StarAlgEquiv`.
- `Matrix.reindexStarAlgEquiv_apply`: simp lemma unfolding to `submatrix`.
-/

@[expose] public section

namespace Matrix

variable {m n : Type*} (R A : Type*)
variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]

/-- For square matrices with coefficients in a star module over a semiring, the natural
map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is an equivalence of star algebras. -/
def reindexStarAlgEquiv (e : m ≃ n) : Matrix m m A ≃⋆ₐ[R] Matrix n n A :=
  { Matrix.reindex e e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    map_mul' M N := by
      ext
      simp_rw [mul_apply]
      refine Fintype.sum_equiv e _ _ ?_
      intro k; simp
    map_star' M := by
      ext; simp [Matrix.submatrix_apply] }

@[simp]
theorem reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexStarAlgEquiv R A e M = M.submatrix e.symm e.symm := rfl

end Matrix
