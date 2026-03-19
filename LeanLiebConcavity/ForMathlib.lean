import LeanLiebConcavity.Defs

/-!
# Candidates for upstream contribution.
-/
/-- harmless but convenient: (0 < a) : a ^ half * a ^ half = a -/
@[simp]
theorem mul_self_half {a : ℝ} (ha : 0 < a) :
    a ^ (1/2 : ℝ) * a ^ (1/2 : ℝ) = a := by
  rw [<- Real.rpow_add ha]
  ring_nf
  exact Real.rpow_one a

-- TODO: ? upstream to Mathlib.Algebra.Star.SelfAdjoint
namespace IsSelfAdjoint

variable {A : Type*} [Mul A] [StarMul A]

/-- If `a` and `b` are self-adjoint, then `star (a * b) = b * a`. -/
lemma star_mul_eq {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    star (a * b) = b * a := by
  grind [star_mul, IsSelfAdjoint.star_eq]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end IsSelfAdjoint

-- TODO: ? upstream to Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

namespace CFC

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `a` is strictly positive and `f` is continuous and maps positive reals to positive reals,
then `cfc f a` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_pos
    {f : ℝ → ℝ} {a : A}
    (ha : IsStrictlyPositive a)
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x)
    (hf_cont : ContinuousOn f (spectrum ℝ a)) :
    IsStrictlyPositive (cfc f a) := by
  have := (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha).2
  exact (cfc_isStrictlyPositive_iff f a hf_cont ha.1.isSelfAdjoint).mpr
    fun x hx => hf_pos (this x hx)

/-- If `g` is continuous on `[0,∞)`, strictly positive on `(0,∞)`, and `R` is strictly
positive, then `cfc g R` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_nonneg
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x)
    {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (cfc f a) :=
  cfc_isStrictlyPositive_of_pos ha hf_pos
    (hf_cont.mono (fun _ hx => spectrum_nonneg_of_nonneg ha.nonneg hx))

/-- existing `smul_pow` only applies to natural number powers -/
protected theorem smul_pow {a : ℝ} (ha : 0 ≤ a) {x : A} (hx : 0 ≤ x) {r : ℝ} (hr : 0 ≤ r) :
    (a • x) ^ r = a ^ r • x ^ r := by
  have hf : ContinuousOn (· ^ r : ℝ → ℝ) ((a • ·) '' spectrum ℝ x) :=
    (Real.continuous_rpow_const hr).continuousOn.mono (by
      rintro _ ⟨t, ht, rfl⟩
      exact smul_nonneg ha (spectrum_nonneg_of_nonneg hx ht))
  rw [rpow_eq_cfc_real (smul_nonneg ha hx), ← cfc_comp_smul a (· ^ r : ℝ → ℝ) x hf]
  simp_rw [smul_eq_mul]
  rw [cfc_congr (fun t ht => Real.mul_rpow ha (spectrum_nonneg_of_nonneg hx ht)),
      cfc_const_mul (a ^ r) (· ^ r) x, ← rpow_eq_cfc_real hx]

open Set

lemma nonneg_iff_spec_nonneg :
    ∀ (a : A), IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0 ↔ 0 ≤ a :=
    fun a =>
      ⟨fun ⟨ha, hs⟩ => (StarOrderedRing.nonneg_iff_spectrum_nonneg a ha).mpr (by simpa using hs),
      fun h => ⟨h.isSelfAdjoint,
                by simpa using (StarOrderedRing.nonneg_iff_spectrum_nonneg a).mp h⟩⟩

--- non-mathlib
theorem operatorConvex_on_nonneg
    {f : ℝ → ℝ} (hf : OperatorConvexOn.{u} (Ici 0) f) :
    ConvexOn ℝ {a : A | 0 ≤ a} (cfc f) := by
  have : {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0} = {a : A | 0 ≤ a} :=
    ext nonneg_iff_spec_nonneg
  exact this ▸ operatorConvex_apply hf

theorem operatorConcave_on_nonneg
    {f : ℝ → ℝ} (hf : OperatorConcaveOn.{u} (Ici 0) f) :
    ConcaveOn ℝ {a : A | 0 ≤ a} (cfc f) := by
  have : {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0} = {a : A | 0 ≤ a} :=
    ext nonneg_iff_spec_nonneg
  exact this ▸ operatorConcave_apply hf

end CFC

section StrictPositivity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
-- TODO: upstream to IsStrictlyPositive or elsewhere?
/-- Convex combinations of strictly positive elements are strictly positive. -/
theorem isStrictlyPositive_convex_combination
    {a b : ℝ} {x y : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : IsStrictlyPositive x) (hy : IsStrictlyPositive y) :
    IsStrictlyPositive (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_smul, zero_add] at hab ⊢; rwa [hab, one_smul]
  · exact (hx.smul ha_pos).add_nonneg (smul_nonneg hb hy.nonneg)

theorem isStrictlyPositive_convex :
  Convex ℝ {a : A | IsStrictlyPositive a} :=
    fun _ hx _ hy _ _ ha hb hab =>
      isStrictlyPositive_convex_combination ha hb hab hx hy

end StrictPositivity
