import LeanLiebConcavity.ForMathlib


noncomputable section


universe u

/-- `f : ℝ → ℝ` is *operator convex* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is convex on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConvexOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)

variable {ι : Type*} {B : ι → Type*}
[∀ i, CStarAlgebra (B i)] [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]

def OperatorConvexOn'' (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ i,
    ConvexOn ℝ {a : B i | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)


/-- `f : ℝ → ℝ` is *operator concave* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is concave on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConcaveOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConcaveOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)


 /-some useful(less) api -/

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {f : ℝ → ℝ} {I J : Set ℝ}

theorem operatorConvex_apply (hf : OperatorConvexOn.{u} I f) :
    ConvexOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
  @hf A _ _ _

theorem operatorConcave_apply (hf : OperatorConcaveOn.{u} I f) :
    ConcaveOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
  @hf A _ _ _

-- TODO: put to ForMathlib, reconfiguring typeclass
omit [PartialOrder A] [StarOrderedRing A] in
lemma cfc_neg' (f : ℝ → ℝ) : cfc (-f) = - (cfc f : A → A) :=
  funext fun a => cfc_neg f a

/-- `f` is operator convex on `I` iff `-f` is operator concave on `I`. -/
theorem operatorConvexOn_neg_iff_concaveOn :
    OperatorConvexOn.{u} I f ↔ OperatorConcaveOn.{u} I (-f) := by
  constructor
  · intro h B _ _ _
    rw [cfc_neg']; exact neg_concaveOn_iff.mpr (@h B _ _ _)
  · intro h B _ _ _
    have hB := @h B _ _ _
    apply neg_concaveOn_iff.mp
    rwa [cfc_neg'] at hB

theorem operatorConcaveOn_neg_iff_convexOn :
    OperatorConcaveOn.{u} I f ↔ OperatorConvexOn.{u} I (-f) := by
  rw [operatorConvexOn_neg_iff_concaveOn, neg_neg]

open Set

theorem operatorConvex_on_nonneg (hf : OperatorConvexOn.{u} (Ici 0) f) :
    ConvexOn ℝ {a : A | 0 ≤ a} (cfc f) := by
  have : {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0} = {a : A | 0 ≤ a} :=
    ext CFC.nonneg_iff_spec_nonneg
  exact this ▸ operatorConvex_apply hf

theorem operatorConcave_on_nonneg (hf : OperatorConcaveOn.{u} (Ici 0) f) :
    ConcaveOn ℝ {a : A | 0 ≤ a} (cfc f) := by
  have : {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0} = {a : A | 0 ≤ a} :=
    ext CFC.nonneg_iff_spec_nonneg
  exact this ▸ operatorConcave_apply hf


/-- If `f` is operator convex on `I`, it is operator convex on any convex subset `J` of `I`. -/
theorem OperatorConvexOn.subset (hf : OperatorConvexOn.{u} I f)
    (hJ : Convex ℝ J) (hJI : J ⊆ I) :
    OperatorConvexOn.{u} J f :=
  fun {B} [_] [_] [_] =>
    ConvexOn.subset (@hf B _ _ _)
      (fun _ ⟨h_sa, h_spec⟩ => ⟨h_sa, h_spec.trans hJI⟩)
      (convex_selfAdjoint_spectrum_subset hJ)

/-- If `f` is operator concave on `I`, it is operator concave on any subset `J ⊆ I`. -/
theorem OperatorConcaveOn.subset (hf : OperatorConcaveOn.{u} I f)
    (hJ : Convex ℝ J) (hJI : J ⊆ I) :
    OperatorConcaveOn.{u} J f :=
  fun {B} [_] [_] [_] =>
    ConcaveOn.subset (@hf B _ _ _)
      (fun _ ⟨h_sa, h_spec⟩ => ⟨h_sa, h_spec.trans hJI⟩)
      (convex_selfAdjoint_spectrum_subset hJ)

section positive
open NNReal
--helpful? definition for operator convexity of positive elements only

def OperatorConcaveOn_pos (f : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConcaveOn ℝ {a : B | 0 ≤ a} (cfc f)

end positive


local notation "½" => (1/2 : ℝ)

-- [def:gen_perspective] Ebadian–Nikoufar–Eshaghi Gordji 2011, generalized perspective function
-- (f △ g)(L, R) ≔ g(R)^{1/2} f(g(R)^{-1/2} L g(R)^{-1/2}) g(R)^{1/2}
/-- The *generalized perspective function* associated to `f h : ℝ → ℝ` -/
def GenPerspective (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f g : ℝ → ℝ) : A × A → A :=
  fun (L, R) ↦
    cfc g R ^ ½ * cfc f (cfc g R ^ (-½) * L * cfc g R ^ (-½)) * cfc g R ^ ½


variable (f g : ℝ → ℝ)
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Negating `f` negates the generalized perspective:
    `((-f) △ g)(L, R) = -(f △ g)(L, R)`. -/
theorem GenPerspective_neg {a : A × A} :
    GenPerspective A (fun x ↦ -(f x)) g a = - GenPerspective A f g a := by
  simp_rw [GenPerspective, cfc_neg]; simp

example (a : A × A) : GenPerspective A (-f) g a = - GenPerspective A f g a :=
  GenPerspective_neg f g

/-- Function-level version of `GenPerspective_neg`. -/
theorem GenPerspective_neg' :
    GenPerspective A (-f) g = -(GenPerspective A f g) :=
  funext fun _ => GenPerspective_neg f g


variable [IsTopologicalRing A] [T2Space A]
open CFC

/-- When `L` and `R` commute and `cfc g R` is strictly positive, the generalized perspective
simplifies: `(f △ g)(L, R) = cfc g R * cfc f (L * (cfc g R) ^ (-1 : ℝ))` -/
theorem GenPerspective_of_commute {L R : A} (hLR : Commute L R)
    (hR : IsStrictlyPositive (cfc g R)) :
    GenPerspective A f g (L, R) = cfc f (L * (cfc g R) ^ (-1 : ℝ)) * cfc g R := by
  dsimp only [GenPerspective]
  set S := cfc g R
  set Si := S ^ (-1 : ℝ)
  have hSL      : Commute S L := (hLR.symm.cfc_real g)
  have hSL_half : Commute (S ^ (-½)) L := hSL.rpow_left (-½)
  have hSSi     : Commute S Si := (Commute.refl S).rpow_right (-1)
  have hfS      : Commute (cfc f (L * Si)) S := hSL.mul_right hSSi |>.symm.cfc_real f
  have hfS_half : Commute (cfc f (L * Si)) (S ^ ½) := hfS.rpow_right ½
  calc S ^ ½ * cfc f (S ^ (-½) * L * S ^ (-½)) * S ^ ½
      = S ^ ½ * cfc f (L * S ^ (-½) * S ^ (-½)) * S ^ ½ := by rw [hSL_half.eq]
    _ = S ^ ½ * cfc f (L * S ^ (-½ + -½)) * S ^ ½ := by simp_rw [mul_assoc, rpow_add hR.isUnit]
    _ = S ^ ½ * cfc f (L * Si) * S ^ ½ := by dsimp only [Si]; norm_num
    _ = cfc f (L * Si) * S := by rw [← hfS_half.eq, mul_assoc, mul_self_rpow_half hR]

theorem GenPerspective_of_rpow_commute {L R : A} {α β : ℝ} (hLR : Commute L R)
    (hL : 0 ≤ L) (hR : IsStrictlyPositive R) (hβ : β ≠ 0) :
    GenPerspective A (· ^ α) (· ^ β) (L, R) = L ^ α * R ^ (β * (1 - α)) := by
  have hR₀ := hR.isUnit
  have hRn := hR.nonneg
  have hRβ_sp : IsStrictlyPositive (cfc (· ^ β) R) :=
    rpow_eq_cfc_real (A := A) hRn (y := β) ▸ hR.rpow
  have hLRnβ_comm : Commute L (R ^ (β * -1)) := hLR.rpow_right _
  calc GenPerspective A (· ^ α) (· ^ β) (L, R)
      = cfc (· ^ α) (L * (cfc (· ^ β) R) ^ (-1 : ℝ)) * cfc (· ^ β) R := by
          rw [GenPerspective_of_commute (· ^ α) (· ^ β) hLR hRβ_sp]
    _ = cfc (· ^ α) (L * R ^ (β * -1)) * R ^ β := by
          rw [← rpow_eq_cfc_real hRn,
              rpow_rpow R β (-1 : ℝ) hR₀ hβ hRn]
    _ = (L * R ^ (β * -1)) ^ α * R ^ β := by
          rw [← rpow_eq_cfc_real <| hLRnβ_comm.mul_nonneg hL hR.rpow.nonneg]
    _ = L ^ α * (R ^ (β * -1)) ^ α * R ^ β := by
          rw [mul_rpow_of_commute hLRnβ_comm hL hR.rpow.nonneg]
    _ = L ^ α * R ^ (β * -1 * α) * R ^ β := by
          rw [rpow_rpow R (β * -1) α hR₀ (by positivity) hRn]
    _ = L ^ α * R ^ (β * (1 - α)) := by
          rw [mul_assoc, ← rpow_add hR₀]; congr 2; ring
