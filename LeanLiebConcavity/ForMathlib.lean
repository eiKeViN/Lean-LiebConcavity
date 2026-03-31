import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Lemmas missing from Mathlib

Collected here for potential upstream contribution. Grouped by topic.
-/

/-! ### Real rpow -/

/-- `x ↦ x ^ r` is continuous on `(0, ∞)` for any `r : ℝ`. -/
theorem rpow_continuousOn_pos {r : ℝ} : ContinuousOn (fun (x : ℝ) ↦ x ^ r) (Set.Ioi 0) :=
  continuousOn_id.rpow_const (by grind only [= Set.mem_Ioi, = id.eq_1])

/-- For `0 < a`, `a ^ ½ * a ^ ½ = a`. -/
@[simp]
theorem mul_self_half {a : ℝ} (ha : 0 < a) :
    a ^ (1/2 : ℝ) * a ^ (1/2 : ℝ) = a := by
  rw [← Real.rpow_add ha]; ring_nf; exact Real.rpow_one a

/-! ### Self-adjointness -/

namespace IsSelfAdjoint

variable {A : Type*} [Mul A] [StarMul A]

/-- If `a` and `b` are self-adjoint, then `star (a * b) = b * a`. -/
@[simp]
lemma star_mul_eq {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    star (a * b) = b * a := by
  rw [star_mul, star_eq ha, star_eq hb]

end IsSelfAdjoint

/-! ### CFC — additional lemmas -/

namespace CFC

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- Nonnegativity in terms of spectrum: `0 ≤ a ↔ a` is self-adjoint with nonneg spectrum. -/
lemma nonneg_iff_spec_nonneg :
    ∀ (a : A), IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Ici 0 ↔ 0 ≤ a :=
  fun a =>
    ⟨fun ⟨ha, hs⟩ => (StarOrderedRing.nonneg_iff_spectrum_nonneg a ha).mpr (by simpa using hs),
     fun h => ⟨h.isSelfAdjoint,
               by simpa using (StarOrderedRing.nonneg_iff_spectrum_nonneg a).mp h⟩⟩

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

/-- For commuting nonneg elements `a b` and any `r : ℝ`, `(a * b) ^ r = a ^ r * b ^ r`. -/
theorem mul_rpow_of_commute {a b : A} (hab : Commute a b)
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) (r : ℝ) :
    (a * b) ^ r = a ^ r * b ^ r := by
  sorry

end CFC

/-! ### Strict positivity -/

section StrictPositivity

--- open NNReal
variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra ℝ A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- Generalization of `CStarAlgebra.isUnit_of_le`: if `a` is strictly positive and `a ≤ b`,
then `b` is a unit. Does not require `CStarAlgebra`; only needs CFC + NonnegSpectrumClass. -/
private lemma isUnit_of_le_general (a : A) {b : A} (hab : a ≤ b)
    (h : IsStrictlyPositive a := by cfc_tac) : IsUnit b := by
  have ha := h.nonneg
  have hb := ha.trans hab
  nontriviality A
  rw [← spectrum.zero_notMem_iff ℝ]
  obtain ⟨r, hr, hr_le⟩ :=
    CFC.exists_pos_algebraMap_le_iff (.of_nonneg ‹_›) |>.mpr <|
    fun _ hx => h.spectrum_pos hx
  have := algebraMap_le_iff_le_spectrum (.of_nonneg ‹_›) |>.mp <| hr_le.trans hab
  intro hb₀; linarith [this 0 hb₀]

/-- Generalization of `IsStrictlyPositive.of_le`: if `a` is strictly positive and `a ≤ b`,
then `b` is strictly positive. Does not require `CStarAlgebra`. -/
private lemma isStrictlyPositive_of_le {a b : A} (ha : IsStrictlyPositive a) (hab : a ≤ b) :
    IsStrictlyPositive b :=
  ⟨ha.nonneg.trans hab, isUnit_of_le_general a hab ha⟩

/-- Generalization of `IsStrictlyPositive.add_nonneg`: adding a nonneg element to a strictly
positive one stays strictly positive. Does not require `CStarAlgebra`. -/
private lemma isStrictlyPositive_add_nonneg {a b : A}
    (ha : IsStrictlyPositive a) (hb : 0 ≤ b) : IsStrictlyPositive (a + b) :=
  isStrictlyPositive_of_le ha ((le_add_iff_nonneg_right a).mpr hb)

variable [PosSMulMono ℝ A]
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

/-! ### Convexity of self-adjoint elements -/

section SelfAdjointConvexity

variable {R : Type*} [Star R] [TrivialStar R]
variable {A : Type*} [AddMonoid A] [StarAddMonoid A] [SMul R A] [StarModule R A]

/-- Self-adjoint elements are closed under `ℝ`-linear combinations. -/
theorem isSelfAdjoint_linear_comb {a b : R} {x y : A}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    IsSelfAdjoint (a • x + b • y) :=
  (IsSelfAdjoint.all _).smul hx |>.add <| (IsSelfAdjoint.all _).smul hy

/-- The set of self-adjoint elements is convex. -/
theorem convex_isSelfAdjoint {A : Type*} [CStarAlgebra A] :
    Convex ℝ {a : A | IsSelfAdjoint a} :=
  (selfAdjoint.submodule ℝ A).convex

end SelfAdjointConvexity

/-! ### Spectrum convexity under linear combinations -/

section SpectrumConvexity


variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
theorem algebraMap_mul_eq_smul {a r : R} :
    algebraMap R A (a * r) = a • algebraMap R A r := by
  simp only [Algebra.algebraMap_eq_smul_one, smul_smul]

theorem algebraMap_smul_eq_smul {a r : R} :
    algebraMap R A (a • r) = a • algebraMap R A r := by
  rw [smul_eq_mul, algebraMap_mul_eq_smul]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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
  obtain ⟨hx_lo, hx_hi⟩ := spectral_bounds x hx_sa hxc
  obtain ⟨hy_lo, hy_hi⟩ := spectral_bounds y hy_sa hyc
  have hinf_I := hI (hx_spec <| hxc.sInf_mem hnx) (hy_spec <| hyc.sInf_mem hny) ha hb hab
  have hsup_I := hI (hx_spec <| hxc.sSup_mem hnx) (hy_spec <| hyc.sSup_mem hny) ha hb hab
  have hsa : IsSelfAdjoint (a • x + b • y) := isSelfAdjoint_linear_comb hx_sa hy_sa
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

end SpectrumConvexity

/-! ### CFC commutativity across two elements -/

section CFCCommute

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

end CFCCommute

section CFCCommuteReal

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [IsTopologicalRing A] [T2Space A]

/-- Real-valued version: if `b` commutes with `a`, then `cfc f a` and `cfc g b` commute for any
`f g : ℝ → ℝ`. No `star` hypotheses are needed since ℝ-CFC is only nontrivial on self-adjoint
elements (where `star a = a`). -/
protected theorem Commute.cfc_cfc_real {a b : A} (hb : Commute a b) (f g : ℝ → ℝ) :
    Commute (cfc f a) (cfc g b) :=
  ((hb.cfc_real f).symm.cfc_real g).symm


end CFCCommuteReal

/-! ### Commute lemmas for real powers (`a ^ r` for `r : ℝ`) -/

section CFCCommuteRpow

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

end CFCCommuteRpow

/-! ### Inner product monotonicity under the Loewner order -/

section LoewnerInnerMono

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma reApplyInnerSelf_mono
    {S T : E →L[𝕜] E} (h : S ≤ T) (x : E) :
    RCLike.re (inner 𝕜 (S x) x) ≤ RCLike.re (inner 𝕜 (T x) x):= by
  have := h.re_inner_nonneg_left x
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub] at this
  linarith

end LoewnerInnerMono
