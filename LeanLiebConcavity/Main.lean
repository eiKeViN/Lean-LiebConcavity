/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import LeanLiebConcavity.Jensen

/-!
# Joint convexity/concavity of generalized perspective functions

This file contains the necessary pieces to prove Lieb's Concavity under the approach of
(generalized) perspective functions.

It also records the sorried statements that the power function `x ↦ x ^ r` is operator convex
(for `1 ≤ r ≤ 2`) and operator concave (for `0 < r ≤ 1`) on `[0, ∞)`.
These sorries are ongoing work by Frédéric Dupuis.

## Main results

- `PowerOperatorConvex` / `PowerOperatorConcave`: the scalar power function `x ↦ x ^ r`
  is operator convex on `[0, ∞)` for `1 ≤ r ≤ 2`, and operator concave for `0 < r ≤ 1`
  (by Löwner's theorem; the CFC-level sorries depend on Mathlib).
- `PerspectiveJointConvex` / `PerspectiveJointConcave`: joint convexity/concavity of
  `GenPerspective A f g` under suitable operator convexity/concavity of `f` and `g`.
- `PowerMeanJointlyConcave` / `PowerMeanJointlyConvex`: the operator `(α,β)`-power mean
  `R #_{(α,β)} L := R^{β/2} (R^{-β/2} L R^{-β/2})^α R^{β/2}` is jointly concave for
  `0 < α, β ≤ 1`, and jointly convex for `1 ≤ α ≤ 2`, `0 < β ≤ 1`.

Note: The working definition of operator power mean appears in `Lieb.lean`;
that one is indexed by the algebra elements rather than operators L and R themselves.

## References

- K. Löwner, *Über monotone Matrixfunktionen*, Math. Z. 38 (1934) 177–216
- F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. 258 (1982) 229–241
- A. Ebadian, I. Nikoufar, M. E. Gordji, *Perspectives of matrix convex functions*,
  PNAS 108 (2011) 7313–7314
- I. Nikoufar, M. Ebadian, M. E. Gordji, *The simplest proof of Lieb concavity theorem*,
  Adv. Math. 248 (2013) 531–533
-/

@[expose] public section

noncomputable section

open Set NNReal CFC

section Loewner

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Mathlib-level statements -/

/-- `x ↦ x ^ r` is operator convex on `[0, ∞)` for `1 ≤ r ≤ 2`. -/
lemma CFC.rpow_operatorConvexOn {r : ℝ} (hr : 1 ≤ r ∧ r ≤ 2) :
    ConvexOn ℝ {a : A | 0 ≤ a} (cfc (fun x : ℝ => x ^ r)) := by
  sorry

/-- `x ↦ x ^ r` is operator concave on `[0, ∞)` for `0 < r ≤ 1`. -/
lemma CFC.rpow_operatorConcaveOn {r : ℝ} (hr : 0 < r ∧ r ≤ 1) :
    ConcaveOn ℝ {a : A | 0 ≤ a} (cfc (fun x : ℝ => x ^ r)) := by
  sorry

/-! ### `OperatorConvexOn/ConcaveOn` statements -/

/-- `x ↦ x ^ r` is operator convex on `[0, ∞)` for `1 ≤ r ≤ 2`. -/
theorem PowerOperatorConvex {r : ℝ} (hr : 1 ≤ r ∧ r ≤ 2) :
    OperatorConvexOn (Ici 0) (· ^ r) := by
  intro B _ _ _
  simp_rw [← nonneg_iff_sa_spectrum_nonneg']
  exact @CFC.rpow_operatorConvexOn B _ _ _ r hr

/-- `x ↦ x ^ r` is operator concave on `[0, ∞)` for `0 < r ≤ 1`. -/
theorem PowerOperatorConcave {r : ℝ} (hr : 0 < r ∧ r ≤ 1) :
    OperatorConcaveOn (Ici 0) (· ^ r) := by
  intro B _ _ _
  simp_rw [← nonneg_iff_sa_spectrum_nonneg']
  exact @CFC.rpow_operatorConcaveOn B _ _ _ r hr

end Loewner

section Perspective

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {f g : ℝ → ℝ}

local notation "½" => (1/2 : ℝ)

/-- The inner conjugation by squareroot identity. -/
private lemma smul_rpow_conj
    {S : A} (hS : IsStrictlyPositive S) {c : ℝ} (hc : 0 < c) (L : A) :
    (c • S) ^ ½ * (S ^ (-½) * L * S ^ (-½)) * (c • S) ^ ½ = c • L := by
  calc (c • S) ^ ½ * (S ^ (-½) * L * S ^ (-½)) * (c • S) ^ ½
      = (c ^ ½ • S ^ ½) * S ^ (-½) * L * S ^ (-½) * (c ^ ½ • S ^ ½) := by
          rw [CFC.smul_pow (le_of_lt hc) hS.nonneg (by linarith)]
          simp only [mul_assoc]
    _ = S ^ ½ * S ^ (-½) * ((c ^ ½ * c ^ ½) • L) * S ^ (-½) * S ^ ½ := by
          simp only [smul_mul_assoc, mul_assoc, mul_smul_comm, smul_smul]
    _ = c • L := by
          grind only [mul_self_half, rpow_neg_mul_rpow', rpow_mul_rpow_neg']

/-- If `f` is operator convex and `g` operator concave, then `f △ g` is jointly convex,
with first entry nonneg and second strictly positive [Eba2011 Thm 2.5]. -/
theorem PerspectiveJointConvex
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0)
    (hg : ContinuousOn g (Ici 0) ∧ ∀ (x : ℝ), 0 < x → 0 < g x)
    (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (hg_opconcav : OperatorConcaveOn.{u} (Ici 0) g) :
    ConvexOn ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2}
      (GenPerspective A f g) := by
  refine ⟨convex_nonneg_strictlyPositive, ?_⟩
  rintro ⟨L₁, R₁⟩ ⟨hL₁, hR₁⟩ ⟨L₂, R₂⟩ ⟨hL₂, hR₂⟩ a b ha hb hab
  rcases ha.eq_or_lt_dec with rfl | ha'
  · simp_all
  rcases hb.eq_or_lt_dec with rfl | hb'
  · simp_all
  -- the main case: 0 < a and 0 < b
  let F : A → A := cfc f
  let G : A → A := cfc g
  -- abbrev + strict positivity of main terms
  have hgR₁ : IsStrictlyPositive (G R₁) := cfc_isStrictlyPositive_of_nonneg hg.1 hg.2 hR₁
  have hgR₂ : IsStrictlyPositive (G R₂) := cfc_isStrictlyPositive_of_nonneg hg.1 hg.2 hR₂
  have hagR₁ : IsStrictlyPositive (a • G R₁) := IsStrictlyPositive.smul ha' hgR₁
  have hbgR₂ : IsStrictlyPositive (b • G R₂) := IsStrictlyPositive.smul hb' hgR₂
  let R := a • R₁ + b • R₂
  have hR : IsStrictlyPositive R := isStrictlyPositive_convex_comb ha hb hab hR₁ hR₂
  have hgR : IsStrictlyPositive (G R) := cfc_isStrictlyPositive_of_nonneg hg.1 hg.2 hR
  let T₁ := (a • G R₁) ^ ½ * G R ^ (-½)
  let T₂ := (b • G R₂) ^ ½ * G R ^ (-½)
  have hT₁_star : star T₁ = G R ^ (-½) * (a • G R₁) ^ ½ := by
    grind only [hagR₁.isSelfAdjoint,
                IsSelfAdjoint.star_mul_eq, rpow_nonneg, IsSelfAdjoint.of_nonneg]
  have hT₂_star : star T₂ = G R ^ (-½) * (b • G R₂) ^ ½ := by
    grind only [hbgR₂.isSelfAdjoint,
                IsSelfAdjoint.star_mul_eq, rpow_nonneg, IsSelfAdjoint.of_nonneg]
  -- uses g's concavity
  have hg_leq : a • G R₁ + b • G R₂ ≤ G R := by
    grind only [show ConcaveOn ℝ {a : A | 0 ≤ a} G from
                operatorConcave_on_nonneg hg_opconcav,
                ConcaveOn, mem_setOf_eq, hR₁.nonneg, hR₂.nonneg]
  -- hT: important condition to apply Jensen
  have hT : star T₁ * T₁ + star T₂ * T₂ ≤ 1 := by
    calc
        star T₁ * T₁ + star T₂ * T₂
      = G R ^ (-½) * (a • G R₁) ^ ½ * (a • G R₁) ^ ½ * G R ^ (-½)
      + G R ^ (-½) * (b • G R₂) ^ ½ * (b • G R₂) ^ ½ * G R ^ (-½) := by
          grind only
    _ = G R ^ (-½) * (a • G R₁) * G R ^ (-½)
      + G R ^ (-½) * (b • G R₂) * G R ^ (-½) := by
          grind only [mul_self_rpow_half hagR₁, mul_self_rpow_half hbgR₂]
    _ = G R ^ (-½) * (a • G R₁ + b • G R₂) * G R ^ (-½) := by
          rw [mul_add, add_mul]
    _ ≤ G R ^ (-½) * G R * G R ^ (-½) :=
          IsSelfAdjoint.of_nonneg (by simp) |>.conjugate_le_conjugate hg_leq
    _ = 1 := by
          grind only [mul_self_rpow_half, rpow_neg_mul_rpow', rpow_mul_rpow_neg']
  have hT₁L₁ :
      star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
      = G R ^ (-½) * (a • L₁) * G R ^ (-½) := by
    calc star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
        = G R ^ (-½)
          * ((a • G R₁) ^ ½ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * (a • G R₁) ^ ½)
          * G R ^ (-½) := by
            grind only
      _ = G R ^ (-½) * (a • L₁) * G R ^ (-½) := by
            rw [smul_rpow_conj hgR₁ ha' L₁]
  have hT₂L₂ :
      star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂
      = G R ^ (-½) * (b • L₂) * G R ^ (-½) := by
    calc star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂
        = G R ^ (-½)
          * ((b • G R₂) ^ ½ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * (b • G R₂) ^ ½)
          * G R ^ (-½) := by
            grind only
      _ = G R ^ (-½) * (b • L₂) * G R ^ (-½) := by
            rw [smul_rpow_conj hgR₂ hb' L₂]
  -- final lemma: applying Jensen
  have hF_jensen :
      F (star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
        + star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂)
      ≤ star T₁ * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
        + star T₂ * F (G R₂ ^ (-½) * L₂ * (G R₂) ^ (-½)) * T₂ := by
    refine JensenOperator_convex_nonneg hf hf_opconvex ⟨?_, ?_⟩ hT
    · exact conjugate_nonneg_of_nonneg hL₁ (by simp)
    · exact conjugate_nonneg_of_nonneg hL₂ (by simp)
  -- main step
  calc
      (GenPerspective A f g) (a • L₁ + b • L₂, a • R₁ + b • R₂)
      = G R ^ ½ * F (G R ^ (-½) * (a • L₁ + b • L₂) * G R ^ (-½)) * G R ^ ½ := by
          dsimp only [GenPerspective]
    _ = G R ^ ½
        * F (G R ^ (-½) * (a • L₁) * G R ^ (-½) + G R ^ (-½) * (b • L₂) * G R ^ (-½))
        * G R ^ ½ := by
          rw [mul_add, add_mul]
    _ = G R ^ ½
        * F (star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
            + star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂)
        * G R ^ ½ := by
          rw [hT₁L₁, hT₂L₂]
    _ ≤ G R ^ ½
        * (star T₁ * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
          + star T₂ * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂)
        * G R ^ ½ :=
          IsSelfAdjoint.of_nonneg (by simp) |>.conjugate_le_conjugate hF_jensen
    _ = G R ^ ½
        * ( G R ^ (-½) * (a • G R₁) ^ ½
            * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½))
            * (a • G R₁) ^ ½ * G R ^ (-½)
          + G R ^ (-½) * (b • G R₂) ^ ½
            * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½))
            * (b • G R₂) ^ ½ * G R ^ (-½))
        * G R ^ ½ := by
          grind only
    _ = G R ^ ½ * G R ^ (-½) * (a • G R₁) ^ ½
        * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½))
        * (a • G R₁) ^ ½
        * (G R ^ (-½) * G R ^ ½)
      + G R ^ ½ * G R ^ (-½) * (b • G R₂) ^ ½
        * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½))
        * (b • G R₂) ^ ½
        * (G R ^ (-½) * G R ^ ½) := by
          simp only [mul_add, add_mul, mul_assoc]
    _ = (a • G R₁) ^ ½ * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * (a • G R₁) ^ ½
        + (b • G R₂) ^ ½ * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * (b • G R₂) ^ ½ := by
          grind only [rpow_neg_mul_rpow', rpow_mul_rpow_neg']
    _ = (a ^ ½ • G R₁ ^ ½) * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * (a ^ ½ • G R₁ ^ ½)
        + (b ^ ½ • G R₂ ^ ½) * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * (b ^ ½ • G R₂ ^ ½) := by
          grind only [CFC.smul_pow, hgR₁.nonneg, hgR₂.nonneg]
    _ = ((a ^ ½ * a ^ ½) • G R₁ ^ ½) * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * G R₁ ^ ½
        + ((b ^ ½ * b ^ ½) • G R₂ ^ ½) * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * G R₂ ^ ½ := by
          simp [smul_smul, mul_assoc]
    _ = a • (G R₁ ^ ½ * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * G R₁ ^ ½)
        + b • (G R₂ ^ ½ * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * G R₂ ^ ½) := by
          grind [mul_self_half, smul_mul_assoc]
    _ = a • (GenPerspective A f g) (L₁, R₁) + b • (GenPerspective A f g) (L₂, R₂) := by
          dsimp only [GenPerspective]

/-- If `f` and `g` are operator concave, then `f △ g` is jointly concave,
with first entry nonneg and second strictly positive [Eba2011 Cor 2.6(i)]. -/
theorem PerspectiveJointConcave
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≥ 0)
    (hg : ContinuousOn g (Ici 0) ∧ ∀ (x : ℝ), 0 < x → 0 < g x)
    (hf_opconcave : OperatorConcaveOn.{u} (Ici 0) f)
    (hg_opconcave : OperatorConcaveOn.{u} (Ici 0) g) :
    ConcaveOn ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2}
      (GenPerspective A f g) := by
  have : ConvexOn ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2}
      (GenPerspective A (-f) g) :=
    PerspectiveJointConvex
      ⟨hf.1.neg, neg_nonpos.mpr hf.2⟩ hg
      (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave)
      hg_opconcave
  rwa [GenPerspective_neg' f g, neg_convexOn_iff] at this

/-- `(α,β)-power mean` is jointly concave for `0 < α, β ≤ 1` [Nik2013 Thm 1.1]. -/
theorem PowerMeanJointlyConcave
    {α β : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) :
    ConcaveOn ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2}
      (GenPerspective A (· ^ α) (· ^ β)) :=
  PerspectiveJointConcave
    ⟨(Real.continuous_rpow_const hα.1.le).continuousOn, by simp [Real.zero_rpow hα.1.ne']⟩
    ⟨(Real.continuous_rpow_const hβ.1.le).continuousOn, fun _ hx => Real.rpow_pos_of_pos hx β⟩
    (PowerOperatorConcave hα)
    (PowerOperatorConcave hβ)

/-- `(α,β)-power mean` is jointly convex for `1 ≤ α ≤ 2` and `0 < β ≤ 1` [Nik2013 Thm 1.1]. -/
theorem PowerMeanJointlyConvex
    {α β : ℝ} (hα : 1 ≤ α ∧ α ≤ 2) (hβ : 0 < β ∧ β ≤ 1) :
    ConvexOn ℝ {p : A × A | 0 ≤ p.1 ∧ IsStrictlyPositive p.2}
      (GenPerspective A (· ^ α) (· ^ β)) :=
  PerspectiveJointConvex
    ⟨(Real.continuous_rpow_const (by linarith)).continuousOn,
     by simp [Real.zero_rpow (by linarith : α ≠ 0)]⟩
    ⟨(Real.continuous_rpow_const hβ.1.le).continuousOn, fun _ hx => Real.rpow_pos_of_pos hx β⟩
    (PowerOperatorConvex hα)
    (PowerOperatorConcave hβ)

end Perspective
