import LeanLiebConcavity.Defs

/-!
# Löwner's theorem: operator convexity/concavity of power functions

This file records that the scalar power function `x ↦ x ^ r` is operator convex
(for `1 ≤ r ≤ 2`) and operator concave (for `0 < r ≤ 1`) on `[0, ∞)`.

The sorries are ongoing work by Frédéric Dupuis.

## References

- K. Löwner, *Über monotone Matrixfunktionen*, Math. Z. 38 (1934) 177–216
- F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. 258 (1982) 229–241
-/

noncomputable section

open Set

section CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ## CFC-level statements (waiting for Mathlib) -/

/-- The power function `x ↦ x ^ r` is operator convex on `[0, ∞)` for `1 ≤ r ≤ 2`. -/
lemma CFC.rpow_operatorConvexOn {r : ℝ} (hr : 1 ≤ r ∧ r ≤ 2) :
    ConvexOn ℝ {a : A | 0 ≤ a} (cfc (fun x : ℝ => x ^ r)) := by
  sorry

/-- The power function `x ↦ x ^ r` is operator concave on `[0, ∞)` for `0 < r ≤ 1`. -/
lemma CFC.rpow_operatorConcaveOn {r : ℝ} (hr : 0 < r ∧ r ≤ 1) :
    ConcaveOn ℝ {a : A | 0 ≤ a} (cfc (fun x : ℝ => x ^ r)) := by
  sorry

end CFC

section Operator

/-! ## Derived using `OperatorConvexOn` / `OperatorConcaveOn` -/

-- [cor:power_convex] Löwner: x ↦ x^r is operator convex on [0,∞) for 1 ≤ r ≤ 2
theorem PowerOperatorConvex {r : ℝ} (hr : 1 ≤ r ∧ r ≤ 2) :
    OperatorConvexOn (Ici 0) (· ^ r) := by
  intro B _ _ _
  simp_rw [← nonneg_iff_sa_spectrum_nonneg']
  exact @CFC.rpow_operatorConvexOn B _ _ _ r hr

-- [cor:power_concave] Löwner: x ↦ x^r is operator concave on [0,∞) for 0 < r ≤ 1
theorem PowerOperatorConcave {r : ℝ} (hr : 0 < r ∧ r ≤ 1) :
    OperatorConcaveOn (Ici 0) (· ^ r) := by
  intro B _ _ _
  simp_rw [← nonneg_iff_sa_spectrum_nonneg']
  exact @CFC.rpow_operatorConcaveOn B _ _ _ r hr

end Operator
