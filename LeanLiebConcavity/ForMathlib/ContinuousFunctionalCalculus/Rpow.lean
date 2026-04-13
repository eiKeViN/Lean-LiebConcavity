module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import LeanLiebConcavity.ForMathlib.ContinuousFunctionalCalculus.Commute
public import LeanLiebConcavity.ForMathlib.ContinuousFunctionalCalculus.Order

/-!
# Real-power (rpow) lemmas missing from Mathlib

Potential upstream contribution to
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`.
-/

@[expose] public section

/-! ### Real rpow -/

/-- For `0 < a`, `a ^ ½ * a ^ ½ = a`. -/
@[simp]
theorem mul_self_half {a : ℝ} (ha : 0 < a) :
    a ^ (1/2 : ℝ) * a ^ (1/2 : ℝ) = a := by
  rw [← Real.rpow_add ha]; ring_nf; exact Real.rpow_one a

/-! ### CFC rpow -/

namespace CFC

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- For strictly positive `x`, `x ^ ½ * x ^ ½ = x`. -/
@[simp]
theorem mul_self_rpow_half {x : A} (hx : IsStrictlyPositive x) :
    x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
  rw [← rpow_add hx.isUnit]; ring_nf; exact rpow_one x

/-- For strictly positive `a`, `a ^ x * a ^ (-x) = 1`. -/
@[simp]
theorem rpow_mul_rpow_neg' {x : ℝ} {a : A} (ha : IsStrictlyPositive a) :
    a ^ x * a ^ (-x) = 1 :=
  rpow_mul_rpow_neg x ha.isUnit

/-- For strictly positive `a`, `a ^ (-x) * a ^ x = 1`. -/
@[simp]
theorem rpow_neg_mul_rpow' {x : ℝ} {a : A} (ha : IsStrictlyPositive a) :
    a ^ (-x) * a ^ x = 1 :=
  rpow_neg_mul_rpow x ha.isUnit

variable [IsTopologicalRing A] [T2Space A]

/-- If `a` is strictly positive and `f` maps positive reals to positive reals (and is continuous
on the spectrum), then `cfc f a` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_pos {f : ℝ → ℝ} {a : A} (ha : IsStrictlyPositive a)
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x) (hf_cont : ContinuousOn f (spectrum ℝ a)) :
    IsStrictlyPositive (cfc f a) := by
  have := CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha |>.2
  exact cfc_isStrictlyPositive_iff f a hf_cont ha.1.isSelfAdjoint |>.mpr
    fun x hx => hf_pos <| this x hx

/-- If `f` is continuous on `[0, ∞)` and maps `(0, ∞)` to `(0, ∞)`, and `a` is strictly
positive, then `cfc f a` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_nonneg {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x) {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (cfc f a) :=
  cfc_isStrictlyPositive_of_pos ha hf_pos <|
    hf_cont.mono <| fun _ hx => spectrum_nonneg_of_nonneg ha.nonneg hx

variable [PosSMulMono ℝ A]

/-- `(a • x) ^ r = a ^ r • x ^ r` for nonneg scalar `a`, nonneg element `x`, and nonneg
exponent `r`. Generalizes `smul_pow` (which only covers natural number exponents). -/
protected theorem smul_pow {a : ℝ} (ha : 0 ≤ a) {x : A} (hx : 0 ≤ x := by cfc_tac)
    {r : ℝ} (hr : 0 ≤ r) : (a • x) ^ r = a ^ r • x ^ r := by
  have hf : ContinuousOn (· ^ r : ℝ → ℝ) ((a • ·) '' spectrum ℝ x) :=
    (Real.continuous_rpow_const hr).continuousOn.mono <| by
      rintro _ ⟨t, ht, rfl⟩
      exact smul_nonneg ha <| spectrum_nonneg_of_nonneg hx ht
  rw [rpow_eq_cfc_real (smul_nonneg ha hx), ← cfc_comp_smul a (· ^ r : ℝ → ℝ) x hf]
  simp_rw [smul_eq_mul]
  rw [cfc_congr <| fun _ ht => Real.mul_rpow ha <| spectrum_nonneg_of_nonneg hx ht,
      cfc_const_mul (a ^ r) (· ^ r) x, ← rpow_eq_cfc_real hx]

section MultiVariate

/-- For commuting nonneg elements `a b` and any `r : ℝ`, `(a * b) ^ r = a ^ r * b ^ r`. -/
-- ADMITTED: This is not currently provable in Mathlib. It would require CFC commutativity
-- for products (i.e., that cfc distributes over multiplication when elements commute),
-- which is not yet available. This lemma is kept as an admitted axiom until Mathlib
-- develops the necessary infrastructure.
theorem mul_rpow_of_commute {a b : A} (hab : Commute a b)
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) (r : ℝ) :
    (a * b) ^ r = a ^ r * b ^ r := by
  sorry

end MultiVariate

end CFC


section Commute

/-! ### Commute lemmas for real powers (`a ^ r` for `r : ℝ`) -/

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
variable [StarOrderedRing A] [Algebra ℝ A] [IsTopologicalRing A] [T2Space A]
variable [NonnegSpectrumClass ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If `a` commutes with `b`, then `a` commutes with `b ^ r` for any `r : ℝ`.
No nonnegativity hypothesis needed: rpow is defined via `ℝ≥0`-CFC, which returns 0 in the
junk case, and `Commute a 0` holds trivially. -/
protected theorem Commute.rpow_right {a b : A} (h : Commute a b) (r : ℝ) :
    Commute a (b ^ r) := by
  simp only [CFC.rpow_def]
  exact (h.symm.cfc_nnreal _).symm

/-- If `a` commutes with `b`, then `a ^ r` commutes with `b` for any `r : ℝ`. -/
protected theorem Commute.rpow_left {a b : A} (h : Commute a b) (r : ℝ) :
    Commute (a ^ r) b :=
  (h.symm.rpow_right r).symm

/-- If `a` and `b` commute, then `a ^ r` and `b ^ s` commute for any `r s : ℝ`. -/
protected theorem Commute.rpow_rpow {a b : A} (h : Commute a b) (r s : ℝ) :
    Commute (a ^ r) (b ^ s) :=
  (h.rpow_left r).rpow_right s

end Commute
