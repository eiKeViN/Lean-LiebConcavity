/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Strict positivity lemmas missing from Mathlib

Potential upstream contribution to
`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order`,
replacing the existing `CStarAlgebra.isUnit_of_le` and `IsStrictlyPositive.of_le`
with versions that do not require `CStarAlgebra` — only CFC + NonnegSpectrumClass.
-/

@[expose] public section

open CFC

section Inv

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra ℝ A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- if `a` is strictly positive and `a ≤ b`, then `b` is a unit. -/
lemma isUnit_of_le_general (a : A) {b : A} (hab : a ≤ b)
    (h : IsStrictlyPositive a := by cfc_tac) : IsUnit b := by
  have ha := h.nonneg
  have hb := ha.trans hab
  nontriviality A
  rw [← spectrum.zero_notMem_iff ℝ]
  obtain ⟨r, hr, hr_le⟩ :=
    exists_pos_algebraMap_le_iff (.of_nonneg ‹_›) |>.mpr <|
    fun _ hx => h.spectrum_pos hx
  have := algebraMap_le_iff_le_spectrum (.of_nonneg ‹_›) |>.mp <| hr_le.trans hab
  intro hb₀; linarith [this 0 hb₀]

/-- if `a` is strictly positive and `a ≤ b`, then `b` is strictly positive. -/
lemma isStrictlyPositive_of_le {a b : A} (ha : IsStrictlyPositive a) (hab : a ≤ b) :
    IsStrictlyPositive b :=
  ⟨ha.nonneg.trans hab, isUnit_of_le_general a hab ha⟩

/-- adding a nonneg element to a strictly positive one stays strictly positive. -/
lemma isStrictlyPositive_add_nonneg {a b : A}
    (ha : IsStrictlyPositive a) (hb : 0 ≤ b) : IsStrictlyPositive (a + b) :=
  isStrictlyPositive_of_le ha ((le_add_iff_nonneg_right a).mpr hb)

/-- adding a strictly positive to a nonneg one stays strictly positive. -/
lemma isStrictlyPositive_nonneg_add {a b : A}
    (ha : 0 ≤ a) (hb : IsStrictlyPositive b) : IsStrictlyPositive (a + b) :=
  add_comm a b ▸ isStrictlyPositive_add_nonneg hb ha

end Inv
