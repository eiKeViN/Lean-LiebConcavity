/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# CFC commutativity lemmas missing from Mathlib

Potential upstream contribution to
`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute`.
-/

@[expose] public section

variable {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [ContinuousFunctionalCalculus 𝕜 A p]
variable [IsTopologicalRing A] [T2Space A]

/-- If `b` commutes with both `a` and `star a`, then `cfc f a` and `cfc g b` commute for any
functions `f` and `g`. Generalizes `cfc_commute_cfc` (same element) to the two-element case. -/
protected theorem Commute.cfc_cfc {a b : A} (hb₁ : Commute a b) (hb₂ : Commute (star a) b)
    (f g : 𝕜 → 𝕜) : Commute (cfc f a) (cfc g b) := by
  have h1 : Commute (cfc f a) b        := hb₁.cfc hb₂ f
  have h2 : Commute (cfc f a) (star b) := hb₂.star_right.cfc hb₁.star_star f
  exact (h1.symm.cfc h2.symm g).symm

/-- For self-adjoint `a`, if `b` commutes with `a` then `cfc f a` and `cfc g b` commute.
The `Commute (star a) b` hypothesis is not needed since `star a = a`. -/
protected theorem IsSelfAdjoint.cfc_cfc {a b : A} (ha : IsSelfAdjoint a) (hb : Commute a b)
    (f g : 𝕜 → 𝕜) : Commute (cfc f a) (cfc g b) :=
  hb.cfc_cfc (ha.star_eq.symm ▸ hb) f g

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A] [T2Space A]

/-- Real-valued version: if `b` commutes with `a`, then `cfc f a` and `cfc g b` commute for any
`f g : ℝ → ℝ`. No `star` hypotheses are needed since ℝ-CFC is only nontrivial on self-adjoint
elements (where `star a = a`). -/
protected theorem Commute.cfc_cfc_real {a b : A} (hb : Commute a b) (f g : ℝ → ℝ) :
    Commute (cfc f a) (cfc g b) :=
  ((hb.cfc_real f).symm.cfc_real g).symm
