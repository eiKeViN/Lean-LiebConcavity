import LeanLiebConcavity.Defs
import LeanLiebConcavity.ConjugateWeightedSum
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

noncomputable section




universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {f : ℝ → ℝ} {I : Set ℝ}

/-! ## Sub-goal 2: The unitary `u` -/
open scoped Matrix

namespace CStarMatrix
/-- The Li–Wu unitary matrix in `CStarMatrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A`.
Constructed from `b : Fin n → A` with `∑ star (b i) * b i = 1`. -/
private def liWuUnitary {n : ℕ} (b : Fin n → A) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A :=
  Matrix.fromBlocks
    (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j)))
    (Matrix.of fun i _ => b i)
    (Matrix.of fun _ j => -(star (b j)))
    (Matrix.of fun _ _ => (0 : A))

omit [PartialOrder A] [StarOrderedRing A] in
private lemma liWuUnitary_star {n : ℕ} (b : Fin n → A) :
    star (liWuUnitary b) = Matrix.fromBlocks
      (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j)))
      (Matrix.of fun i _ => -(b i))
      (Matrix.of fun _ j => star (b j))
      (Matrix.of fun _ _ => (0 : A)) := by
    let X := Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j))
    let Y := Matrix.of fun i (_ : Unit) => b i
    let Z := Matrix.of fun (_ : Unit) j => -(star (b j))
    let W := Matrix.of fun (_ _ : Unit) => (0 : A)
    have hX : Xᴴ
        = (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j))) := by
      ext i j
      simp only [X, Matrix.conjTranspose_apply, Matrix.of_apply,
        apply_ite, ite_eq_left_iff, ite_eq_right_iff,
        star_sub, star_one, star_mul, star_star, star_neg, sub_eq_neg_self]
      split_ifs with h_eq <;> grind only
    have hZ : Zᴴ
        = (Matrix.of fun i _ => -(b i)) := by
      ext i j
      simp only [Z, Matrix.conjTranspose_apply, Matrix.of_apply, star_neg, star_star]
    have hY : Yᴴ
        = (Matrix.of fun _ j => star (b j)) := by
      ext i j
      simp only [Y, Matrix.conjTranspose_apply, Matrix.of_apply]
    have hW : Wᴴ
        = (Matrix.of fun _ _ => (0 : A)) := by
      ext i j
      simp only [W, Matrix.conjTranspose_apply, Matrix.of_apply, star_zero]
    simpa only [hX, hZ, hY, hW] using Matrix.fromBlocks_conjTranspose X Y Z W

/-- The key algebraic identity used to collapse the middle sum when proving `star u * u = 1`:
`∑ k, b i * star (b k) * b k * star (b j) = b i * star (b j)`. -/
private lemma sum_star_mul_cancel {n : ℕ} {B : Type*} [Semiring B] [StarMul B]
    {b : Fin n → B} (hb : ∑ k, star (b k) * b k = 1) (i j : Fin n) :
    ∑ k, b i * star (b k) * b k * star (b j) = b i * star (b j) := by
  conv_lhs =>
    arg 2; ext k
    rw [show b i * star (b k) * b k * star (b j) =
        b i * (star (b k) * b k) * star (b j) from by
      simp only [← mul_assoc]]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hb, mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- `star u * u = 1` for the Li–Wu unitary, using `∑ star (b i) * b i = 1`. -/
private lemma liWuUnitary_star_mul_self' {n : ℕ} {b : Fin n → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    star (liWuUnitary b) * liWuUnitary b = 1 := by
  rw [liWuUnitary_star, liWuUnitary, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  -- After fromBlocks_multiply, goal is: fromBlocks TL TR BL BR = fromBlocks 1 0 0 1
  refine ⟨?_tl, ?_tr, ?_bl, ?_br⟩
  · -- Top-left: (δ - P) * (δ - P) + P = δ,  where P_{ij} = b i * star (b j)
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      neg_mul, mul_neg, neg_neg, Matrix.one_apply]
    have : ∀ k : Fin n,
        (if i = k then 1 - b i * star (b k) else -(b i * star (b k)))
        * (if k = j then 1 - b k * star (b j) else -(b k * star (b j)))
        = (if i = k then if k = j then 1 else 0 else 0)
          - (if i = k then b k * star (b j) else 0)
          - (if k = j then b i * star (b k) else 0)
          + b i * (star (b k) * b k) * star (b j) := by
      intro _
      split_ifs with _ _ <;> simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
      · abel
      · simp only [mul_neg]; abel
      · simp only [neg_mul, mul_assoc]; abel
      · simp only [neg_mul, mul_assoc]; noncomm_ring
    open Finset in
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hb,
              sum_ite_eq, sum_ite_eq', mem_univ, univ_unique, sum_const, card_singleton,
              if_true, sub_add_cancel, one_smul, mul_one]
  · -- Top-right: (δ - P) * Y + (-Y_col) * 0 = 0
    -- Goal: ∑ x, (if i = x then 1 - b i * star(b x) else -(b i * star(b x))) * b x = 0
    ext i (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      mul_zero, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        (if i = x then 1 - b i * star (b x) else -(b i * star (b x))) * b x
        = (if i = x then b x else 0) - b i * (star (b x) * b x) := by
      intro x; split_ifs with h
      · subst h; simp only [sub_mul, one_mul, mul_assoc]
      · simp only [neg_mul, mul_assoc, zero_sub]
    simp_rw [this, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, hb, mul_one, sub_self, Matrix.zero_apply]
  · -- Bottom-left: Z' * (δ - P) + 0 * (-Z') = 0
    -- Goal: ∑ x, star(b x) * (if x = j then 1 - b x * star(b j) else -(b x * star(b j))) = 0
    ext (_ : Unit) j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
              zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        star (b x) * (if x = j then 1 - b x * star (b j) else -(b x * star (b j)))
        = (if x = j then star (b x) else 0) - star (b x) * b x * star (b j) := by
      intro x; split_ifs with h
      · subst h; simp [mul_sub, mul_one, mul_assoc]
      · simp only [mul_neg, mul_assoc, zero_sub]
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
             ← Finset.sum_mul, hb, one_mul, sub_self, Matrix.zero_apply]
  · -- Bottom-right: Z' * Y + 0 * 0 = 1
    ext (_ : Unit) (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
              hb, Finset.univ_unique, mul_zero,
              Finset.sum_const_zero, add_zero, Matrix.one_apply_eq]


omit [PartialOrder A] [StarOrderedRing A] in
/-- `u * star u = 1` for the Li–Wu unitary, using `∑ star (b i) * b i = 1`. -/
private lemma liWuUnitary_mul_star_self' {n : ℕ} {b : Fin n → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    liWuUnitary b * star (liWuUnitary b) = 1 := by
  rw [liWuUnitary_star, liWuUnitary, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_tl, ?_tr, ?_bl, ?_br⟩
  · -- Top-left: X*X + Y*(-Z') = δ,  same algebra as before
    -- X_{ij} = δ_{ij} - P_{ij},  Y_{i,*} = b i,  (-Z')_{*,j} = star(b j)
    -- (X*X)_{ij} = ∑_k X_{ik}*X_{kj}, (Y*(-Z'))_{ij} = b i * star(b j) = P_{ij}
    -- same as TL of star u * u
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    have : ∀ k : Fin n,
        (if i = k then 1 - b i * star (b k) else -(b i * star (b k)))
        * (if k = j then 1 - b k * star (b j) else -(b k * star (b j)))
        = (if i = k then if k = j then 1 else 0 else 0)
          - (if i = k then b k * star (b j) else 0)
          - (if k = j then b i * star (b k) else 0)
          + b i * (star (b k) * b k) * star (b j) := by
      intro _
      split_ifs with _ _ <;> simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
      · abel
      · simp only [mul_neg]; abel
      · simp only [neg_mul, mul_assoc]; abel
      · simp only [neg_mul, mul_assoc]; noncomm_ring
    open Finset in
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hb,
              sum_ite_eq, sum_ite_eq', mem_univ, univ_unique, sum_const, card_singleton,
              if_true, sub_add_cancel, one_smul, mul_one]
  · -- Top-right: X*(-Y) + Y*0 = 0
    -- Goal: ∑ x X_{ix} * (-b x) + b i * 0 = 0, i.e. -∑ x X_{ix} * b x = 0
    -- same sum as TR of star u * u (proved zero), negated
    ext i (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      mul_zero, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        (if i = x then 1 - b i * star (b x) else -(b i * star (b x))) * (-b x)
        = -(if i = x then b x else 0) + b i * (star (b x) * b x) := by
      intro _; split_ifs with h
      · subst h; simp only [mul_neg, sub_mul, one_mul, mul_assoc]; abel
      · simp only [mul_neg, neg_mul, mul_assoc]; abel
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, hb, mul_one, neg_add_cancel, Matrix.zero_apply]
  · -- Bottom-left: Z*X + 0*(-Z') = 0
    -- Goal: ∑ x (-star(b x)) * X_{xj} = 0, i.e. -∑ x star(b x) * X_{xj} = 0
    -- same sum as BL of star u * u (proved zero), negated
    ext (_ : Unit) j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        (-star (b x)) * (if x = j then 1 - b x * star (b j) else -(b x * star (b j)))
        = -(if x = j then star (b x) else 0) + star (b x) * b x * star (b j) := by
      intro _; split_ifs with h
      · subst h; simp only [neg_mul, mul_sub, mul_one, mul_assoc]; abel
      · simp only [neg_mul, mul_neg, mul_assoc]; abel
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul, hb, one_mul, neg_add_cancel, Matrix.zero_apply]
  · -- Bottom-right: Z*(-Y) + 0*0 = 1
    -- Goal: ∑ x (-star(b x)) * (-b x) = 1, i.e. ∑ x star(b x) * b x = 1
    ext (_ : Unit) (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
              neg_mul, mul_neg, neg_neg, zero_mul, Finset.sum_const_zero, add_zero,]
    exact hb

end CStarMatrix
/-! ## General (arbitrary n) Jensen's Operator Inequality -/

/-- **Jensen's Operator Inequality** (Li–Wu 2012, Theorem 2.2, general n):

Let `A` be an ordered unital C⋆-algebra and `f : ℝ → ℝ` a continuous operator convex
function on a convex set `I`.
Suppose:
1. `a : Fin n → A` are self-adjoint with `spectrum ℝ (a i) ⊆ I`.
2. `b : Fin n → A` satisfy `∑ i, star (b i) * b i = 1`.

Then:
`cfc f (∑ i, star (b i) * a i * b i) ≤ ∑ i, star (b i) * cfc f (a i) * b i`.
-/
-- [thm:jensen_2012] Li-Wu 2012, Theorem 2.2 (general n)
theorem JensenOperator_convex_general
    {n : ℕ} {a b : Fin n → A}
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : ∀ i, IsSelfAdjoint (a i))
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i = 1) :
    cfc f (∑ i, star (b i) * a i * b i) ≤
      ∑ i, star (b i) * cfc f (a i) * b i := by
  sorry

-- [thm:jensen_2012'] Li-Wu 2012, Corollary 2.4 (general n)
/-- **Jensen's Operator Inequality, sub-unital version** (Li–Wu 2012, Corollary 2.4):

Same as `JensenOperator_convex_general` but with the weaker hypothesis
`∑ i, star (b i) * b i ≤ 1` and extra conditions `0 ∈ I` and `f 0 ≤ 0`.

Proof idea: extend to `n+1` elements with `b_{n+1} = (1 - ∑ b*b)^{1/2}` and `a_{n+1} = 0`,
apply the `= 1` version, then drop the last term using `f 0 ≤ 0`. -/
theorem JensenOperator_convex_general'
    {n : ℕ} {a b : Fin n → A}
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : ∀ i, IsSelfAdjoint (a i))
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i ≤ 1) :
    cfc f (∑ i, star (b i) * a i * b i) ≤
      ∑ i, star (b i) * cfc f (a i) * b i := by
  sorry

/-! ## n = 2 specializations -/

open Matrix
open Fin
variable {a₁ a₂ b₁ b₂ : A}

/-- Strong Jensen's Operator Inequality, n = 2 case.
Specialization of `JensenOperator_convex_general` to two summands. -/
theorem JensenOperator_convex
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  have := JensenOperator_convex_general hI hf hf_opconvex
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by simpa only [sum_univ_two] using hb)
  simpa only [sum_univ_two] using this

/-- Sub-unital Jensen's Operator Inequality, n = 2 case.
Specialization of `JensenOperator_convex_general'` to two summands. -/
theorem JensenOperator_convex'
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  have := JensenOperator_convex_general' hI hf hf_opconvex
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by simpa only [sum_univ_two] using hb)
  simpa only [sum_univ_two] using this

/-! ## Concave versions (derived by negation) -/

theorem JensenOperator_concave
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  have h := JensenOperator_convex hI hf.neg
    (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave) ha ha_spec hb
  simp only [cfc_neg, mul_neg, neg_mul, ← neg_add] at h
  exact neg_le_neg_iff.mp h


theorem JensenOperator_concave'
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  have h := JensenOperator_convex' hI
    ⟨hf.1.neg, neg_nonpos.mpr hf.2⟩
    (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave) ha ha_spec hb
  simp only [cfc_neg, mul_neg, neg_mul, ← neg_add] at h
  exact neg_le_neg_iff.mp h

open NNReal
open Set

/-- A version applies to nonnegative elements of the C* algebra,
which is useful for our application.
A positive element is always self-adjoint. -/
theorem JensenOperator_convex_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ :=
  JensenOperator_convex'
    ⟨convex_Ici 0, Set.self_mem_Ici⟩
    hf hf_opconvex
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb

theorem JensenOperator_concave_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) :=
  JensenOperator_concave'
    ⟨convex_Ici 0, Set.self_mem_Ici⟩
    hf hf_opconcave
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb
