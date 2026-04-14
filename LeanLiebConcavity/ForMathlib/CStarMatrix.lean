/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Auxiliary `ofMatrix` lemmas for `CStarMatrix`

Follows `CStarMatrix`.
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
