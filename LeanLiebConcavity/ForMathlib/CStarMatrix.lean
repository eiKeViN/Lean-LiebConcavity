module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Auxiliary `ofMatrix` lemmas for `CStarMatrix`

These lemmas relate operations on `Matrix` to the corresponding operations on `CStarMatrix`
via `CStarMatrix.ofMatrix`. They follow the simp-normal form convention of CStarMatrix.lean:
pull `ofMatrix` to the outside.
-/

@[expose] public section

namespace CStarMatrix

open Matrix

variable {m n : Type*} {A : Type*}

@[simp]
theorem ofMatrix_transpose (M : Matrix m n A) :
    ofMatrix Mᵀ = (ofMatrix M).transpose := rfl

@[simp]
theorem ofMatrix_conjTranspose [Star A] (M : Matrix m n A) :
    ofMatrix Mᴴ = (ofMatrix M).conjTranspose := rfl

theorem of_apply (M N : Matrix m n A) (h : M = N) :
    ofMatrix M = ofMatrix N := h
