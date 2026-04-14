/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Inner product monotonicity lemmas missing from Mathlib

Potential upstream contribution to `Mathlib.Analysis.InnerProductSpace.Positive`.

Note: future home is `ForMathlib/InnerProductSpace/Positive.lean` once the
`InnerProductSpace/` subdirectory is created (at which point `Inner.lean` will
also be renamed to `InnerProductSpace/Frobenius.lean`).
-/

@[expose] public section

open RCLike

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma reApplyInnerSelf_mono_right
    {S T : E →L[𝕜] E} (h : S ≤ T) (x : E) :
    re (inner 𝕜 x (S x)) ≤ re (inner 𝕜 x (T x)) := by
  have := h.re_inner_nonneg_right x
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub] at this
  linarith

lemma reApplyInnerSelf_mono_left
    {S T : E →L[𝕜] E} (h : S ≤ T) (x : E) :
    re (inner 𝕜 (S x) x) ≤ re (inner 𝕜 (T x) x) := by
  have := h.re_inner_nonneg_left x
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub] at this
  linarith
