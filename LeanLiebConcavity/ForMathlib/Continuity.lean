module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity lemmas

Specializations of ones in `Mathlib.Analysis.SpecialFunctions.Pow.Continuity`.
-/

@[expose] public section

/-- `x ↦ x ^ r` is continuous on `(0, ∞)` for any `r : ℝ`. -/
theorem rpow_continuousOn_pos {r : ℝ} : ContinuousOn (fun (x : ℝ) ↦ x ^ r) (Set.Ioi 0) :=
  continuousOn_id.rpow_const (by grind only [= Set.mem_Ioi, = id.eq_1])
