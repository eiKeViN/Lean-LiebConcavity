/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Self-adjointness lemmas missing from Mathlib

Potential upstream contribution to `Mathlib.Algebra.Star.SelfAdjoint`.
-/

@[expose] public section

namespace IsSelfAdjoint

variable {A : Type*} [Mul A] [StarMul A]

/-- If `a` and `b` are self-adjoint, then `star (a * b) = b * a`. -/
@[simp]
lemma star_mul_eq {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    star (a * b) = b * a := by
  rw [star_mul, star_eq ha, star_eq hb]

end IsSelfAdjoint

variable {R : Type*} [Star R] [TrivialStar R]
variable {A : Type*} [AddMonoid A] [StarAddMonoid A] [SMul R A] [StarModule R A]

/-- Self-adjoint elements are closed under `R`-linear combinations. -/
theorem isSelfAdjoint_linear_comb {a b : R} {x y : A}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    IsSelfAdjoint (a • x + b • y) :=
  (IsSelfAdjoint.all _).smul hx |>.add <| (IsSelfAdjoint.all _).smul hy
