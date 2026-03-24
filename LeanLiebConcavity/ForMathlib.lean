import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

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
@[simp]
lemma star_mul_eq {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    star (a * b) = b * a := by
  rw [star_mul, star_eq ha, star_eq hb]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end IsSelfAdjoint

-- TODO: ? upstream to Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital / rpow
namespace CFC

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

lemma nonneg_iff_spec_nonneg :
    ∀ (a : A), IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Ici 0 ↔ 0 ≤ a :=
    fun a =>
      ⟨fun ⟨ha, hs⟩ => (StarOrderedRing.nonneg_iff_spectrum_nonneg a ha).mpr (by simpa using hs),
      fun h => ⟨h.isSelfAdjoint,
                by simpa using (StarOrderedRing.nonneg_iff_spectrum_nonneg a).mp h⟩⟩

/-- CFC analogue of `mul_self_half`: for strictly positive `x`, `x ^ ½ * x ^ ½ = x`. -/
@[simp]
theorem mul_self_rpow_half
    {x : A} (hx : IsStrictlyPositive x) :
    x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
  rw [← rpow_add hx.isUnit]
  ring_nf
  exact rpow_one x

/-- versions of `rpow_mul_rpow_neg` and `rpow_neg_mul_rpow`
that takes single hypothesis: strict positive -/
@[simp]
theorem rpow_mul_rpow_neg' {x : ℝ} {a : A} (ha : IsStrictlyPositive a) :
    a ^ x * a ^ (-x) = 1 :=
  rpow_mul_rpow_neg x ha.isUnit

@[simp]
theorem rpow_neg_mul_rpow' {x : ℝ} {a : A} (ha : IsStrictlyPositive a) :
    a ^ (-x) * a ^ x = 1 :=
  rpow_neg_mul_rpow x ha.isUnit

variable [IsTopologicalRing A] [T2Space A]
/-- If `a` is strictly positive and `f` is continuous and maps positive reals to positive reals,
then `cfc f a` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_pos
    {f : ℝ → ℝ} {a : A}
    (ha : IsStrictlyPositive a)
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x)
    (hf_cont : ContinuousOn f (spectrum ℝ a)) :
    IsStrictlyPositive (cfc f a) := by
  have := CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp ha |>.2
  exact cfc_isStrictlyPositive_iff f a hf_cont ha.1.isSelfAdjoint |>.mpr
    fun x hx => hf_pos <| this x hx

/-- If `g` is continuous on `[0,∞)`, strictly positive on `(0,∞)`, and `R` is strictly
positive, then `cfc g R` is strictly positive. -/
theorem cfc_isStrictlyPositive_of_nonneg
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_pos : ∀ ⦃x : ℝ⦄, 0 < x → 0 < f x)
    {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (cfc f a) :=
  cfc_isStrictlyPositive_of_pos ha hf_pos <|
    hf_cont.mono <| fun _ hx => spectrum_nonneg_of_nonneg ha.nonneg hx

variable [PosSMulMono ℝ A]
/-- existing `smul_pow` only applies to natural number powers -/
protected theorem smul_pow {a : ℝ} (ha : 0 ≤ a)
    {x : A} (hx : 0 ≤ x := by cfc_tac)
    {r : ℝ} (hr : 0 ≤ r) :
    (a • x) ^ r = a ^ r • x ^ r := by
  have hf : ContinuousOn (· ^ r : ℝ → ℝ) ((a • ·) '' spectrum ℝ x) :=
    (Real.continuous_rpow_const hr).continuousOn.mono <| by
      rintro _ ⟨t, ht, rfl⟩
      exact smul_nonneg ha <| spectrum_nonneg_of_nonneg hx ht
  rw [rpow_eq_cfc_real (smul_nonneg ha hx), ← cfc_comp_smul a (· ^ r : ℝ → ℝ) x hf]
  simp_rw [smul_eq_mul]
  rw [cfc_congr <| fun t ht => Real.mul_rpow ha <| spectrum_nonneg_of_nonneg hx ht,
      cfc_const_mul (a ^ r) (· ^ r) x, ← rpow_eq_cfc_real hx]

end CFC

section StrictPositivity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
-- TODO: upstream to IsStrictlyPositive or elsewhere?
/-- Convex combinations of strictly positive elements are strictly positive. -/
theorem isStrictlyPositive_convex_comb
    {a b : ℝ} {x y : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : IsStrictlyPositive x) (hy : IsStrictlyPositive y) :
    IsStrictlyPositive (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_smul, zero_add] at hab ⊢; rwa [hab, one_smul]
  · exact (hx.smul ha_pos).add_nonneg <| smul_nonneg hb hy.nonneg

theorem isStrictlyPositive_convex :
  Convex ℝ {a : A | IsStrictlyPositive a} :=
    fun _ hx _ hy _ _ ha hb hab =>
      isStrictlyPositive_convex_comb ha hb hab hx hy

/-- The product set `{(L, R) | 0 ≤ L ∧ IsStrictlyPositive R}` is convex,
used in statement of joint concavity/convexity -/
theorem convex_nonneg_strictlyPositive :
    Convex ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2} := by
  have : {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2}
      = Set.Ici 0 ×ˢ {a : A | IsStrictlyPositive a} :=
    Set.ext fun _ => Iff.rfl
  rw [this]
  exact (convex_Ici 0).prod isStrictlyPositive_convex

end StrictPositivity

section SelfAdjointConvexity

variable {R : Type*} [Star R] [TrivialStar R]
variable {A : Type*} [AddMonoid A] [StarAddMonoid A] [SMul R A] [StarModule R A]

/-- Self-adjoint elements are closed under linear combinations (hence convex combinations) -/
theorem isSelfAdjoint_linear_comb
    {a b : R} {x y : A}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    IsSelfAdjoint (a • x + b • y) :=
  (IsSelfAdjoint.all _).smul hx |>.add <| (IsSelfAdjoint.all _).smul hy

/-- The set of self-adjoint elements is convex. -/
theorem convex_isSelfAdjoint {A : Type*} [CStarAlgebra A] :
    Convex ℝ {a : A | IsSelfAdjoint a} :=
  (selfAdjoint.submodule ℝ A).convex

end SelfAdjointConvexity

section SpectrumConvexity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Set

/-- If `I ⊆ ℝ` is convex and `x, y` are self-adjoint with spectra in `I`, then any
convex combination `a • x + b • y` also has spectrum in `I`. -/
theorem spectrum_subset_convex_comb
    {I : Set ℝ} (hI : Convex ℝ I)
    {a b : ℝ} {x y : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : IsSelfAdjoint x ∧ spectrum ℝ x ⊆ I)
    (hy : IsSelfAdjoint y ∧ spectrum ℝ y ⊆ I) :
    spectrum ℝ (a • x + b • y) ⊆ I := by
  obtain ⟨hx_sa, hx_spec⟩ := hx
  obtain ⟨hy_sa, hy_spec⟩ := hy
  -- handling singleton algebra wherein all spectra are empty
  by_cases hA : Nontrivial A
  swap
  · rw [not_nontrivial_iff_subsingleton] at hA; simp
  -- remaining case: spectra are non-empty; also compact
  have hxc := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) x
  have hyc := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) y
  -- algebraMap ordering bounds
  have hx_lo : algebraMap ℝ A (sInf (spectrum ℝ x)) ≤ x :=
    (algebraMap_le_iff_le_spectrum).mpr fun _ hs => csInf_le hxc.bddBelow hs
  have hy_lo : algebraMap ℝ A (sInf (spectrum ℝ y)) ≤ y :=
    (algebraMap_le_iff_le_spectrum).mpr fun _ hs => csInf_le hyc.bddBelow hs
  have hx_hi : x ≤ algebraMap ℝ A (sSup (spectrum ℝ x)) :=
    (le_algebraMap_iff_spectrum_le).mpr fun _ hs => le_csSup hxc.bddAbove hs
  have hy_hi : y ≤ algebraMap ℝ A (sSup (spectrum ℝ y)) :=
    (le_algebraMap_iff_spectrum_le).mpr fun _ hs => le_csSup hyc.bddAbove hs
  have alg_eq : ∀ {r s : ℝ}, algebraMap ℝ A (a * r + b * s) =
      a • algebraMap ℝ A r + b • algebraMap ℝ A s := by
    intro r s; simp only [map_add, Algebra.algebraMap_eq_smul_one, smul_smul]
  -- For any spectral value, it lies between the convex combinations of extrema
  intro t ht
  have hnx := CFC.spectrum_nonempty ℝ x
  have hny := CFC.spectrum_nonempty ℝ y
  have hl_I : a • sInf (spectrum ℝ x) + b • sInf (spectrum ℝ y) ∈ I := by
    refine hI ?_ ?_ ha hb hab
    · exact hx_spec <| hxc.sInf_mem hnx
    · exact hy_spec <| hyc.sInf_mem hny
  have hu_I : a • sSup (spectrum ℝ x) + b • sSup (spectrum ℝ y) ∈ I := by
    refine hI ?_ ?_ ha hb hab
    · exact hx_spec <| hxc.sSup_mem hnx
    · exact hy_spec <| hyc.sSup_mem hny
  have lower : algebraMap ℝ A (a * sInf (spectrum ℝ x) + b * sInf (spectrum ℝ y))
      ≤ a • x + b • y := by
    rw [alg_eq]
    exact add_le_add (smul_le_smul_of_nonneg_left hx_lo ha)
                     (smul_le_smul_of_nonneg_left hy_lo hb)
  have upper : a • x + b • y
      ≤ algebraMap ℝ A (a * sSup (spectrum ℝ x) + b * sSup (spectrum ℝ y)) := by
    rw [alg_eq]
    exact add_le_add (smul_le_smul_of_nonneg_left hx_hi ha)
                     (smul_le_smul_of_nonneg_left hy_hi hb)
  have : IsSelfAdjoint (a • x + b • y) := isSelfAdjoint_linear_comb hx_sa hy_sa
  refine hI.ordConnected.out hl_I hu_I ⟨?_, ?_⟩
  · exact (algebraMap_le_iff_le_spectrum this).mp lower t ht
  · exact (le_algebraMap_iff_spectrum_le this).mp upper t ht

/-- The set of self-adjoint elements with spectrum in a convex set is convex. -/
theorem convex_selfAdjoint_spectrum_subset
    {I : Set ℝ} (hI : Convex ℝ I) :
    Convex ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} :=
  fun _ hx _ hy _ _ ha hb hab =>
    ⟨isSelfAdjoint_linear_comb hx.1 hy.1,
     spectrum_subset_convex_comb hI ha hb hab hx hy⟩

end SpectrumConvexity
