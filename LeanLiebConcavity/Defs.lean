import LeanLiebConcavity.ForMathlib


noncomputable section

namespace CFC

universe u

/-- `f : ℝ → ℝ` is *operator convex* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is convex on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConvexOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)

/-- `f : ℝ → ℝ` is *operator concave* on `I : Set ℝ` if, for every unital C⋆-algebra `B`
with a compatible partial order, `cfc f` is concave on the set of self-adjoint elements of
`B` whose spectrum is contained in `I`. -/
def OperatorConcaveOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B],
    ConcaveOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f)


 /-some useful(less) api -/
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
theorem operatorConvex_apply
    {f : ℝ → ℝ} {I : Set ℝ} (hf : OperatorConvexOn.{u} I f) :
    ConvexOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
  @hf A _ _ _

theorem operatorConcave_apply
    {f : ℝ → ℝ} {I : Set ℝ} (hf : OperatorConcaveOn.{u} I f) :
    ConcaveOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
  @hf A _ _ _

lemma cfc_neg' (f : ℝ → ℝ) : cfc (-f) = - (cfc f : A → A) :=
  funext fun a => cfc_neg f a

/-- `f` is operator convex on `I` iff `-f` is operator concave on `I`. -/
theorem operatorConvexOn_neg_iff_concaveOn {I : Set ℝ} {f : ℝ → ℝ} :
    OperatorConvexOn.{u} I f ↔ OperatorConcaveOn.{u} I (-f) := by
  constructor
  · intro h B _ _ _
    have : cfc (-f) = -(cfc f : B → B) := funext fun a => cfc_neg f a
    rw [this]; exact neg_concaveOn_iff.mpr (@h B _ _ _)
  · intro h B _ _ _
    have hB := @h B _ _ _
    rw [show cfc (-f) = -(cfc f : B → B) from funext fun a => cfc_neg f a] at hB
    exact neg_concaveOn_iff.mp hB

theorem operatorConcaveOn_neg_iff_convexOn {I : Set ℝ} {f : ℝ → ℝ} :
    OperatorConcaveOn.{u} I f ↔ OperatorConvexOn.{u} I (-f) := by
  rw [operatorConvexOn_neg_iff_concaveOn, neg_neg]

open Set

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

section positive
open NNReal
--helpful definition for operator convexity of positive elements only

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
variable (a : A × A)

/-- Negating `f` negates the generalized perspective:
    `((-f) △ g)(L, R) = -(f △ g)(L, R)`. -/
theorem GenPerspective_neg :
    GenPerspective A (fun x ↦ -(f x)) g a = - GenPerspective A f g a := by
  simp_rw [GenPerspective, cfc_neg]; simp

example : GenPerspective A (-f) g a = - GenPerspective A f g a := GenPerspective_neg f g a

end CFC

variable (a : ℝ)

example : ℝ → ℝ := fun x ↦ x ^ a
