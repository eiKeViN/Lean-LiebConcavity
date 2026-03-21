import LeanLiebConcavity.Jensen

/-- now need properties of Hermitian matrices -/
example : 1 = 1 := rfl

noncomputable section


namespace CFC
open Set
open NNReal

--namespace IsSelfAdjoint
universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {L₁ L₂ R₁ R₂ : A}
variable {f g : ℝ → ℝ}

local notation "½" => (1/2 : ℝ)

/-- The inner conjugation identity: contracting `L` through `(c • S)^{1/2}` and `S^{-1/2}`
collapses to `c • L`. Used twice in `PerspectiveJointConvex`. -/
private lemma smul_rpow_conj
    {S : A} (hS : IsStrictlyPositive S) {c : ℝ} (hc : 0 < c) (L : A) :
    (c • S) ^ ½ * (S ^ (-½) * L * S ^ (-½)) * (c • S) ^ ½ = c • L := by
  calc (c • S) ^ ½ * (S ^ (-½) * L * S ^ (-½)) * (c • S) ^ ½
      = (c ^ ½ • S ^ ½) * S ^ (-½) * L * S ^ (-½) * (c ^ ½ • S ^ ½) := by
          rw [CFC.smul_pow (le_of_lt hc) hS.nonneg (by linarith)]; grind only
    _ = S ^ ½ * S ^ (-½) * ((c ^ ½ * c ^ ½) • L) * S ^ (-½) * S ^ ½ := by
          simp [smul_smul, mul_assoc]
    _ = c ^ (½ + ½) • L := by
          grind only [= Real.rpow_add, rpow_neg_mul_rpow, rpow_mul_rpow_neg,
            IsStrictlyPositive.iff_of_unital]
    _ = c • L := by grind only [Real.rpow_one]

theorem PerspectiveJointConvex
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0)
    (hg : ContinuousOn g (Ici 0) ∧ ∀ ⦃x : ℝ⦄, 0 < x → 0 < g x)
    (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (hg_opconcav : OperatorConcaveOn.{u} (Ici 0) g)
    (hL : 0 ≤ L₁ ∧ 0 ≤ L₂)
    (hR₁ : IsStrictlyPositive R₁) (hR₂ : IsStrictlyPositive R₂) :
    ∀⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (GenPerspective A f g) (a • L₁ + b • L₂, a • R₁ + b • R₂)
      ≤ a • (GenPerspective A f g) (L₁, R₁) + b • (GenPerspective A f g) (L₂, R₂) := by
  intros a b ha hb hab
  rcases ha.eq_or_lt_dec with rfl | ha'
  · -- a = 0
    simp_all
  rcases hb.eq_or_lt_dec with rfl | hb'
  · -- b = 0
    simp_all
  -- the main case: 0 < a and 0 < b
  let F : A → A := cfc f
  let G : A → A := cfc g
  -- abbrev + strict positivity of main terms
  have hgR₁ : IsStrictlyPositive (G R₁) := cfc_isStrictlyPositive_of_nonneg hg.1 hg.2 hR₁
  have hgR₂ : IsStrictlyPositive (G R₂) := cfc_isStrictlyPositive_of_nonneg hg.1 hg.2 hR₂
  have hagR₁ : IsStrictlyPositive (a • cfc g R₁) :=
    IsStrictlyPositive.smul ha' hgR₁
  have hbgR₂ : IsStrictlyPositive (b • cfc g R₂) :=
    IsStrictlyPositive.smul hb' hgR₂
  let R := a • R₁ + b • R₂
  have hR : IsStrictlyPositive R := by grind only [isStrictlyPositive_convex_combination]
  have hgR : IsStrictlyPositive (cfc g R) :=
    (cfc_isStrictlyPositive_of_nonneg hg.1 hg.2 hR)
  let T₁ := (a • G R₁) ^ ½ * G R ^ (-½)
  let T₂ := (b • G R₂) ^ ½ * G R ^ (-½)
  have hT₁_star : star T₁ = G R ^ (-½) * (a • G R₁) ^ ½ := by
    grind only [hagR₁.isSelfAdjoint,
                IsSelfAdjoint.star_mul_eq, rpow_nonneg, IsSelfAdjoint.of_nonneg]
  have hT₂_star : star T₂ = G R ^ (-½) * (b • G R₂) ^ ½ := by
    grind only [hbgR₂.isSelfAdjoint,
                IsSelfAdjoint.star_mul_eq, rpow_nonneg, IsSelfAdjoint.of_nonneg]
  -- uses g's concavity
  have : a • G R₁ + b • G R₂ ≤ G R := by
    have : ConcaveOn ℝ {a : A | 0 ≤ a} (G) := operatorConcave_on_nonneg hg_opconcav
    grind only [ConcaveOn, mem_setOf_eq, hR₁.nonneg, hR₂.nonneg]
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
          grind only
    _ ≤ G R ^ (-½) * G R * G R ^ (-½) := by
          exact (IsSelfAdjoint.of_nonneg (by simp)).conjugate_le_conjugate (this)
    _ = 1 := by
          grind only [mul_self_rpow_half, rpow_neg_mul_rpow', rpow_mul_rpow_neg']
  have hT₁L₁ :
      star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
      = G R ^ (-½) * (a • L₁) * G R ^ (-½) := by
    calc star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
        = G R ^ (-½) * ((a • G R₁) ^ ½ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * (a • G R₁) ^ ½)
          * G R ^ (-½) := by
            grind only
      _ = G R ^ (-½) * (a • L₁) * G R ^ (-½) := by
            rw [smul_rpow_conj hgR₁ ha' L₁]
  have hT₂L₂ :
      star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂
      = G R ^ (-½) * (b • L₂) * G R ^ (-½) := by
    calc star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂
        = G R ^ (-½) * ((b • G R₂) ^ ½ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * (b • G R₂) ^ ½)
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
    refine JensenOperator2012_convex_nonneg hf hf_opconvex ⟨?_, ?_⟩ hT
    · exact conjugate_nonneg_of_nonneg hL.1 (by simp)
    · exact conjugate_nonneg_of_nonneg hL.2 (by simp)
  -- main step
  calc
      (GenPerspective A f g) (a • L₁ + b • L₂, a • R₁ + b • R₂)
      = G R ^ ½ * F (G R ^ (-½) * (a • L₁ + b • L₂) * G R ^ (-½)) * G R ^ ½ := by
          grind only [GenPerspective]
    _ = G R ^ ½ * F (G R ^ (-½) * (a • L₁) * G R ^ (-½)
                    + G R ^ (-½) * (b • L₂) * G R ^ (-½))
                * G R ^ ½ := by
          congr; grind only
    _ = G R ^ ½ * F (star T₁ * (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
                        + star T₂ * (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂)
                * G R ^ ½ := by
          simp_rw [hT₁L₁, hT₂L₂]
    _ ≤ G R ^ ½ * (star T₁ * F (G R₁ ^ (-½) * L₁ * G R₁ ^ (-½)) * T₁
                    + star T₂ * F (G R₂ ^ (-½) * L₂ * G R₂ ^ (-½)) * T₂)
                * G R ^ ½ := by
          exact (IsSelfAdjoint.of_nonneg (by simp)).conjugate_le_conjugate hF_jensen
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
          grind only
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
          grind only [GenPerspective]


variable (r : ℝ)
example : 0 ≤ L₁ ^ r := by simp
example : IsSelfAdjoint (cfc f L₁) := by simp
example : IsSelfAdjoint (L₁ ^ r) := IsSelfAdjoint.of_nonneg (by simp)
example : (1 / 2: ℝ) + 1 / 2 = (1 : ℝ) := add_halves 1

set_option grind.debug true

example {a b c d : A} : a * b * d + a * c * d= a * (b + c) * d := by grind only
example {a : A} (ha : IsUnit a) (ha' : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) * a ^ (-1 : ℝ) = 1 := by
  grind [rpow_neg_mul_rpow (-1) ha ha']
example {a : A} (ha : IsStrictlyPositive a) : IsUnit a := IsStrictlyPositive.isUnit ha
example : 0 ≤ ½ := by linarith

theorem PerspectiveJointConcave : 1 + 1 = 2 := by rfl


end CFC
