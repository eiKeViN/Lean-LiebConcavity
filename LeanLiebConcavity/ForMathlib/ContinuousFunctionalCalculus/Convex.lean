/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import LeanLiebConcavity.ForMathlib.SelfAdjoint
public import LeanLiebConcavity.ForMathlib.ContinuousFunctionalCalculus.Order

/-!
# Convexity lemmas missing from Mathlib

Convexity results for strictly positive elements and self-adjoint elements with
constrained spectrum.
-/

@[expose] public section

/-! ### Convexity of strictly positive elements -/

section StrictPositivity

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra ℝ A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PosSMulMono ℝ A]

/-- Convex combinations of strictly positive elements are strictly positive. -/
theorem isStrictlyPositive_convex_comb {a b : ℝ} {x y : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : IsStrictlyPositive x) (hy : IsStrictlyPositive y) :
    IsStrictlyPositive (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_smul, zero_add] at hab ⊢; rwa [hab, one_smul]
  · exact isStrictlyPositive_add_nonneg (hx.smul ha_pos) (smul_nonneg hb hy.nonneg)

/-- The set of strictly positive elements is convex. -/
theorem convex_isStrictlyPositive :
    Convex ℝ {a : A | IsStrictlyPositive a} :=
  fun _ hx _ hy _ _ ha hb hab => isStrictlyPositive_convex_comb ha hb hab hx hy

/-- The set `{(L, R) | 0 ≤ L ∧ IsStrictlyPositive R}` is convex. -/
theorem convex_nonneg_strictlyPositive :
    Convex ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2} := by
  simpa only [Set.setOf_and] using
    (convex_Ici 0).prod convex_isStrictlyPositive

theorem convex_strictlyPositive_nonneg :
    Convex ℝ {p : A × A | IsStrictlyPositive p.1 ∧ 0 ≤ p.2} := by
  simpa only [Set.setOf_and] using
    convex_isStrictlyPositive.prod (convex_Ici 0)

/-- The set `{(A, B) | IsStrictlyPositive A ∧ IsStrictlyPositive B}` is convex. -/
theorem convex_strictlyPositive_prod :
    Convex ℝ {p : A × A | IsStrictlyPositive p.1 ∧ IsStrictlyPositive p.2} := by
  simpa only [Set.setOf_and] using
    convex_isStrictlyPositive.prod convex_isStrictlyPositive

end StrictPositivity

/-! ### Convexity of self-adjoint elements and spectrum -/

section AlgebraMap

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
theorem algebraMap_mul_eq_smul {a r : R} :
    algebraMap R A (a * r) = a • algebraMap R A r := by
  simp only [Algebra.algebraMap_eq_smul_one, smul_smul]

theorem algebraMap_smul_eq_smul {a r : R} :
    algebraMap R A (a • r) = a • algebraMap R A r := by
  rw [smul_eq_mul, algebraMap_mul_eq_smul]

end AlgebraMap

section Spectrum

variable {A : Type*} [CStarAlgebra A]

/-- The set of self-adjoint elements is convex. -/
theorem convex_isSelfAdjoint :
    Convex ℝ {a : A | IsSelfAdjoint a} :=
  (selfAdjoint.submodule ℝ A).convex

variable [PartialOrder A] [StarOrderedRing A]

theorem spectral_bounds (z : A) (hz_sa : IsSelfAdjoint z) (hzc : IsCompact (spectrum ℝ z)) :
    algebraMap ℝ A (sInf (spectrum ℝ z)) ≤ z ∧
    z ≤ algebraMap ℝ A (sSup (spectrum ℝ z)) := by
  constructor
  · exact (algebraMap_le_iff_le_spectrum hz_sa).mpr fun _ hs =>
      csInf_le hzc.bddBelow hs
  · exact (le_algebraMap_iff_spectrum_le hz_sa).mpr fun _ hs =>
      le_csSup hzc.bddAbove hs

/-- If `x` and `y` are self-adjoint with spectra in a convex set `I`, then any convex
combination `a • x + b • y` also has spectrum in `I`. -/
theorem spectrum_subset_convex_comb {I : Set ℝ} (hI : Convex ℝ I)
    {a b : ℝ} {x y : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : IsSelfAdjoint x ∧ spectrum ℝ x ⊆ I)
    (hy : IsSelfAdjoint y ∧ spectrum ℝ y ⊆ I) :
    spectrum ℝ (a • x + b • y) ⊆ I := by
  obtain ⟨hx_sa, hx_spec⟩ := hx
  obtain ⟨hy_sa, hy_spec⟩ := hy
  by_cases hA : Nontrivial A
  swap
  · rw [not_nontrivial_iff_subsingleton] at hA; simp
  have hxc := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) x
  have hyc := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) y
  have hnx := CFC.spectrum_nonempty ℝ x
  have hny := CFC.spectrum_nonempty ℝ y
  have hsa : IsSelfAdjoint (a • x + b • y) := isSelfAdjoint_linear_comb hx_sa hy_sa
  have hinf_I := hI (hx_spec <| hxc.sInf_mem hnx) (hy_spec <| hyc.sInf_mem hny) ha hb hab
  have hsup_I := hI (hx_spec <| hxc.sSup_mem hnx) (hy_spec <| hyc.sSup_mem hny) ha hb hab
  obtain ⟨hx_lo, hx_hi⟩ := spectral_bounds x hx_sa hxc
  obtain ⟨hy_lo, hy_hi⟩ := spectral_bounds y hy_sa hyc
  intro t ht
  refine hI.ordConnected.out hinf_I hsup_I
    ⟨(algebraMap_le_iff_le_spectrum hsa).mp ?_ t ht,
    (le_algebraMap_iff_spectrum_le hsa).mp ?_ t ht⟩
  all_goals
    simp_rw [map_add, algebraMap_smul_eq_smul]
    gcongr

/-- The set of self-adjoint elements with spectrum in a convex set `I` is convex. -/
theorem convex_selfAdjoint_spectrum_subset {I : Set ℝ} (hI : Convex ℝ I) :
    Convex ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} := by
  intro _ hx _ hy _ _ ha hb hab
  exact ⟨isSelfAdjoint_linear_comb hx.1 hy.1, spectrum_subset_convex_comb hI ha hb hab hx hy⟩

end Spectrum
