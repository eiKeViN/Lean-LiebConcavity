/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Lemmas missing from `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`

Potential upstream contribution to
`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`.
-/

@[expose] public section

section CFC

variable {A : Type*}
  [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-- `0 ≤ a`if and only if `a` is self-adjoint with nonneg spectrum. -/
lemma nonneg_iff_sa_spectrum_nonneg {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ ∀ x ∈ spectrum ℝ a, 0 ≤ x :=
  ⟨fun h => ⟨h.isSelfAdjoint, (StarOrderedRing.nonneg_iff_spectrum_nonneg a).mp h⟩,
    fun ⟨ha, hs⟩ => (StarOrderedRing.nonneg_iff_spectrum_nonneg a ha).mpr hs⟩

lemma nonneg_iff_sa_spectrum_nonneg' {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Ici 0 :=
  nonneg_iff_sa_spectrum_nonneg

end CFC
