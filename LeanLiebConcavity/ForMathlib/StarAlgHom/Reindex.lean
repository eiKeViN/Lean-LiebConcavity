/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# `Matrix.reindex` as ring/star-ring/star-algebra equivalences

Mathlib provides `Matrix.reindexLinearEquiv` and `Matrix.reindexAlgEquiv`, but the latter
requires `[CommSemiring R]` and `[DecidableEq]`. This file fills the gaps in the hierarchy:

| Variant | This file? | Assumptions on `R` | `DecidableEq`? | Star? |
|---------|------------|--------------------|----------------|-------|
| `reindexLinearEquiv` | Mathlib | `[Semiring R]` | No | No |
| `reindexAlgEquiv` | Mathlib | `[CommSemiring R]` | Yes | No |
| `reindexRingEquiv` | Here | — | No | No |
| `reindexStarRingEquiv` | Here | — | No | Yes |
| `reindexStarAlgEquiv` | Here | none (R phantom, `[SMul R A]`) | No | Yes |

## Main declarations

- `Matrix.reindexRingEquiv`: `Matrix.reindex e e` as a `RingEquiv`.
- `Matrix.reindexStarRingEquiv`: `Matrix.reindex e e` as a `StarRingEquiv`.
- `Matrix.reindexStarAlgEquiv`: `Matrix.reindex e e` as a `StarAlgEquiv`.
-/

@[expose] public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section Ring

variable (A : Type*) [NonUnitalNonAssocSemiring A]

/-- `Matrix.reindex e e` as a `RingEquiv`. -/
def reindexRingEquiv (e : m ≃ n) : Matrix m m A ≃+* Matrix n n A :=
  { Matrix.reindex e e with
    map_add' := fun _ _ => rfl
    map_mul' := fun M N => by
      ext; simp_rw [mul_apply]; exact Fintype.sum_equiv e _ _ fun k => by simp }

@[simp]
theorem reindexRingEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexRingEquiv A e M = M.submatrix e.symm e.symm := rfl

end Ring

section StarRing

variable (A : Type*) [NonUnitalNonAssocSemiring A] [Star A]

/-- `Matrix.reindex e e` as a `StarRingEquiv`. -/
def reindexStarRingEquiv (e : m ≃ n) : Matrix m m A ≃⋆+* Matrix n n A :=
  { reindexRingEquiv A e with
    map_star' := fun M => by ext; simp [Matrix.submatrix_apply] }

@[simp]
theorem reindexStarRingEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexStarRingEquiv A e M = M.submatrix e.symm e.symm := rfl

end StarRing

section StarAlg

variable (R A : Type*) [NonUnitalNonAssocSemiring A] [SMul R A] [Star A]

/-- `Matrix.reindex e e` as a `StarAlgEquiv`. -/
def reindexStarAlgEquiv (e : m ≃ n) : Matrix m m A ≃⋆ₐ[R] Matrix n n A :=
  { reindexStarRingEquiv A e with
    map_smul' := fun _ _ => rfl }

@[simp]
theorem reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexStarAlgEquiv R A e M = M.submatrix e.symm e.symm := rfl

end StarAlg

end Matrix
