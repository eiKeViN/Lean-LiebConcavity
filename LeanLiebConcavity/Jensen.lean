/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import LeanLiebConcavity.Defs
public import LeanLiebConcavity.ConjugateWeightedSum
public import LeanLiebConcavity.ForMathlib.StarAlgHom.Diagonal
public import LeanLiebConcavity.ForMathlib.StarAlgHom.Unitary
public import LeanLiebConcavity.ForMathlib.StarAlgHom.Reindex
public import LeanLiebConcavity.FourierAveraging

/-!
# Jensen's operator inequality

Jensen's inequality for operator convex functions, following the proof strategy of
Li–Wu (2014) via unitary conjugation in block matrices.

## Main results

- `JensenOperator_convex_general`: the general form with n-ary sums.
- `JensenOperator_convex/_concave`: the standard binary sum forms.
- `JensenOperator_convex_nonneg/_concave_nonneg`: versions on `[0, ∞)`.

## References

- X. Li, W. Wu, *Operator Jensen's Inequality on C⋆-algebras*,
  Act. Math. Sinica 30 (2013) 35-50
- F. Hansen, G. K. Pedersen, *Jensen's Inequality for Operators and Lowner's Theorem*,
  Math. Ann. 258 (1982) 229-241
-/

noncomputable section

universe u
variable {A : Type u} [CStarAlgebra A]

/-! ## Sub-goal 2: The unitary `u` -/

section Unitary

open scoped Matrix

/-- The Li–Wu unitary matrix in `CStarMatrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A`.
Constructed from `b : Fin n → A` with `∑ star (b i) * b i = 1`. -/
private def U {n : ℕ} (b : Fin n → A) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A :=
  Matrix.fromBlocks
    (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j)))
    (Matrix.of fun i _ => b i)
    (Matrix.of fun _ j => -(star (b j)))
    (Matrix.of fun _ _ => (0 : A))

private lemma U_star {n : ℕ} (b : Fin n → A) :
    star (U b) = Matrix.fromBlocks
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

private lemma U_tl_entry {n : ℕ} {b : Fin n → A} (i j k : Fin n) :
    (if i = k then 1 - b i * star (b k) else -(b i * star (b k)))
    * (if k = j then 1 - b k * star (b j) else -(b k * star (b j)))
    = (if i = k then if k = j then 1 else 0 else 0)
      - (if i = k then b k * star (b j) else 0)
      - (if k = j then b i * star (b k) else 0)
      + b i * (star (b k) * b k) * star (b j) := by
  split_ifs with _ _ <;> simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
  · abel
  · simp only [mul_neg]; abel
  · simp only [neg_mul, mul_assoc]; abel
  · simp only [neg_mul, mul_assoc]; noncomm_ring

/-- `star u * u = 1` when `∑ star (b i) * b i = 1`. -/
private lemma U_star_mul_self' {n : ℕ} {b : Fin n → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    star (U b) * U b = 1 := by
  rw [U_star, U, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_tl, ?_tr, ?_bl, ?_br⟩
  · -- Top-left: (δ - P) * (δ - P) + P = δ,  where P_{ij} = b i * star (b j)
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
      neg_mul, mul_neg, neg_neg]
    open Finset in
    simp only [U_tl_entry i j, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
      sum_ite_eq, sum_ite_eq', mem_univ, univ_unique, sum_const, card_singleton,
      hb, if_true, sub_add_cancel, one_smul, mul_one]
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
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, ← Finset.mul_sum, hb, mul_one, sub_self, Matrix.zero_apply]
  · -- Bottom-left: Z' * (δ - P) + 0 * (-Z') = 0
    ext (_ : Unit) j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
              zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        star (b x) * (if x = j then 1 - b x * star (b j) else -(b x * star (b j)))
        = (if x = j then star (b x) else 0) - star (b x) * b x * star (b j) := by
      intro x; split_ifs with h
      · subst h; simp only [mul_sub, mul_one, mul_assoc]
      · simp only [mul_neg, mul_assoc, zero_sub]
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, ← Finset.sum_mul, hb, one_mul, sub_self, Matrix.zero_apply]
  · -- Bottom-right: Z' * Y + 0 * 0 = 1
    ext (_ : Unit) (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
      Finset.univ_unique, mul_zero, Finset.sum_const_zero, add_zero, hb]

/-- `u * star u = 1` when `∑ star (b i) * b i = 1`. -/
private lemma U_mul_star_self' {n : ℕ} {b : Fin n → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    U b * star (U b) = 1 := by
  rw [U_star, U, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_tl, ?_tr, ?_bl, ?_br⟩
  · -- Top-left: X * X + Y * (-Z') = δ
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    open Finset in
    simp only [U_tl_entry i j, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hb,
              sum_ite_eq, sum_ite_eq', mem_univ, univ_unique, sum_const, card_singleton,
              if_true, sub_add_cancel, one_smul, mul_one]
  · -- Top-right: X * (-Y) + Y * 0 = 0
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
  · -- Bottom-left: Z * X + 0 * (-Z') = 0
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
  · -- Bottom-right: Z * (-Y) + 0 * 0 = 1
    ext (_ : Unit) (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
              neg_mul, mul_neg, neg_neg, zero_mul, Finset.sum_const_zero, add_zero, hb]

/-- `U b` is a member of the unitary subgroup. -/
private theorem U_mem_unitary {n : ℕ} {b : Fin (n + 1) → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    U b ∈ unitary _ :=
  Unitary.mem_iff.mpr ⟨U_star_mul_self' hb, U_mul_star_self' hb⟩

end Unitary

open MatCStar

/-! ### The Li–Wu diagonal matrix -/

section Prelim

/-- `diag(a 0, …, a n, a n)`: `a : Fin (n+1) → A` supplies the n+1 values going to the
`Fin (n + 1)` slot and the last `a (Fin.last n)` goes in the `Unit` slot. -/
private def Diag {n : ℕ} (a : Fin (n + 1) → A) :
    Matrix (Fin (n + 1) ⊕ Unit) (Fin (n + 1) ⊕ Unit) A :=
  Matrix.diagonal (Sum.elim (fun i => a i) (fun _ => a (Fin.last n)))

/-- `Diag a` is self-adjoint when each `a i` is. -/
private theorem Diag_isSelfAdjoint {n : ℕ} {a : Fin (n + 1) → A}
    (ha : ∀ i, IsSelfAdjoint (a i)) :
    IsSelfAdjoint (Diag a) :=
  isSelfAdjoint_diagonal_sum_elim ha (ha (Fin.last n))

/-- The spectrum of `Diag a` is contained in `I` when each `spectrum ℝ (a i) ⊆ I`. -/
private theorem Diag_spectrum_subset {n : ℕ} {a : Fin (n + 1) → A} {I : Set ℝ}
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I) :
    spectrum ℝ (Diag a) ⊆ I := by
  apply MatCStar.spectrum_diagonal_subset
  rintro (j | ⟨⟩)
  · exact ha_spec j
  · exact ha_spec (Fin.last n)

/-- The bottom-right `(Unit, Unit)` corner of `star u * Diag a * u` equals
`∑ i, star (b i) * a i * b i`. -/
private lemma StarU_Diag_U_BR {n : ℕ} {b : Fin (n + 1) → A} (a : Fin (n + 1) → A) :
    (star (U b) * Diag a * U b) (Sum.inr ()) (Sum.inr ()) =
      ∑ i, star (b i) * a i * b i := by
  rw [U_star, U]
  simp only [Matrix.mul_apply, Diag, Matrix.diagonal_apply, Fintype.sum_sum_type]
  -- evaluate fromBlocks entries
  simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
             Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  -- the Unit-indexed terms vanish (inr () entry of u's last col is 0)
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
             Finset.univ_unique, Sum.inl.injEq]
  congr 1; ext x
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The last diagonal entry of `star u * Diag a * u` is `∑ i, star (b i) * a i * b i`. -/
private theorem StarU_Diag_U_last {n : ℕ} (a b : Fin (n + 1) → A) :
    (star (U b) * Diag a * U b).diag (Sum.inr ()) =
      ∑ i, star (b i) * a i * b i := StarU_Diag_U_BR a

end Prelim

section CFC

variable [PartialOrder A] [StarOrderedRing A]

/-- CFC acts entry-wise on the Li–Wu diagonal lift. -/
private theorem Diag_cfc {n : ℕ} {a : Fin (n + 1) → A} {f : ℝ → ℝ}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (a i)))
    (hsa : ∀ i, IsSelfAdjoint (a i)) :
    cfc f (Diag a) = Diag (fun i => cfc f (a i)) := by
  dsimp only [Diag]
  let d : Fin (n + 1) ⊕ Unit → A := Sum.elim (fun i => a i) (fun _ => a (Fin.last n))
  have spectrum_eq : (⋃ i : Fin (n + 1) ⊕ Unit, spectrum ℝ (d i)) = ⋃ i, spectrum ℝ (a i) := by
    ext; simp only [Set.mem_iUnion, d]
    constructor
    · intro ⟨i, hi⟩
      rcases i with j | ⟨⟩
      · exact ⟨j, hi⟩
      · exact ⟨Fin.last n, hi⟩
    · exact fun ⟨i, hi⟩ => ⟨Sum.inl i, hi⟩
  have hf' : ContinuousOn f (⋃ i, spectrum ℝ (d i)) := spectrum_eq ▸ hf
  have hd : ∀ i, IsSelfAdjoint (d i) := fun i =>
    match i with
    | Sum.inl j => hsa j
    | Sum.inr () => hsa (Fin.last n)
  rw [cfc_diagonal hf' hd]
  ext i; match i with
  | Sum.inl j => rfl
  | Sum.inr () => rfl

/-- Specialization of `Diag_cfc` to the `ContinuousOn I` assumption -/
private theorem Diag_cfc_contI {n : ℕ} {a : Fin (n + 1) → A} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : ContinuousOn f I)
    (hsa : ∀ i, IsSelfAdjoint (a i)) (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I) :
    cfc f (Diag a) = Diag (fun i => cfc f (a i)) := by
  apply Diag_cfc
  · exact hf.mono (Set.iUnion_subset ha_spec)
  · exact hsa

end CFC

/-! ## Sub-goal 3 (Fourier averaging) -/

section Defs

open Complex

private abbrev Theta (n : ℕ) : ℂ :=
  exp (2 * ↑Real.pi * Complex.I / ↑(n + 1))

private lemma Theta_isPrimitiveRoot (n : ℕ) :
    IsPrimitiveRoot (Theta n) (n + 1) :=
  isPrimitiveRoot_exp (n + 1) (by positivity)

/-- The `k`-th Fourier diagonal matrix over `Fin n ⊕ Unit`.
Entry at `inl j` is `θ^(k*j) • 1`, entry at `inr ()` is `θ^(k*n) • 1`. -/
private abbrev V {n : ℕ} (k : Fin (n + 1)) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A :=
  Matrix.diagonal fun i => match i with
    | Sum.inl j => (Theta n ^ (k.val * j.val) : ℂ) • (1 : A)
    | Sum.inr () => (Theta n ^ (k.val * n) : ℂ) • (1 : A)

end Defs

section Equiv

/-- reindexing Fin (n + 1) ⊕ Unit ≃ Fin (n + 2) -/
private abbrev SumUnitEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv

private lemma SumUnitEquiv_symm_castSucc {n : ℕ} (i : Fin n) :
    (SumUnitEquiv n).symm (Fin.castSucc i) = Sum.inl i := by
  apply (SumUnitEquiv n).injective
  simp

private lemma SumUnitEquiv_symm_last {n : ℕ} :
    (SumUnitEquiv n).symm (Fin.last n) = Sum.inr () := by
  apply (SumUnitEquiv n).injective
  simp; rfl

open Matrix

@[simp]
theorem reindex_diagonal {n : ℕ}
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A) :
    (reindexStarAlgEquiv ℝ A (SumUnitEquiv n)) (diagonal M.diag) =
      diagonal ((reindexStarAlgEquiv ℝ A (SumUnitEquiv n) M).diag) := by simp

/-- FourierMatrix is the reindexed version of V k -/
private lemma reindex_V_eq_FourierMatrix {n : ℕ} (k : Fin (n + 1)) :
    (reindexStarAlgEquiv ℝ A (SumUnitEquiv n)) (V (A := A) k) =
      FourierMatrix (Theta n) A k := by
  ext i j
  simp only [reindexStarAlgEquiv_apply, FourierMatrix, submatrix_apply,
             diagonal_apply]
  refine Fin.lastCases ?_ (fun _ => ?_) i <;> refine Fin.lastCases ?_ (fun _ => ?_) j
  all_goals
    simp only [SumUnitEquiv_symm_castSucc, SumUnitEquiv_symm_last]
    simp [Fin.ext_iff, Fin.last, Fin.castSucc]
    try omega

end Equiv

section FourierAvg

open Matrix

/-- `V k` is a member of the unitary subgroup, deduced from `FourierMatrix_mem_unitary`
via the `reindexStarAlgEquiv` transfer. -/
private theorem V_mem_unitary {n : ℕ} (k : Fin (n + 1)) :
    V (A := A) k ∈ unitary (Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A) := by
  let φ := reindexStarAlgEquiv ℝ A (SumUnitEquiv n)
  have hF : FourierMatrix (Theta n) A k ∈ unitary _ :=
    FourierMatrix_mem_unitary (Theta_isPrimitiveRoot n) (Nat.succ_ne_zero n)
  have hmem := Unitary.map_mem (StarAlgHomClass.toStarAlgHom φ.symm) hF
  have hinv : (StarAlgHomClass.toStarAlgHom φ.symm) (φ (V k)) = V k := φ.symm_apply_apply (V k)
  rwa [← reindex_V_eq_FourierMatrix, hinv] at hmem

/-- The Fourier average of `M` equals `diagonal (Matrix.diag M)`. -/
private theorem V_avg_diag {n : ℕ}
    (M : Matrix (Fin (n + 1) ⊕ Unit) (Fin (n + 1) ⊕ Unit) A) :
    ∑ k : Fin (n + 2), (1 / (↑(n + 2) : ℝ)) •
        (star (V (A := A) k) * M * V (A := A) k) = diagonal M.diag := by
  let φ := reindexStarAlgEquiv ℝ A (SumUnitEquiv (n + 1))
  apply φ.injective
  change φ (∑ k : Fin (n + 2), (1 / (↑(n + 2) : ℝ)) • (star (V k) * M * V k)) =
         φ (diagonal M.diag)
  simp only [map_sum, map_smul, map_mul, map_star,
    φ, reindex_V_eq_FourierMatrix, reindex_diagonal]
  exact FourierAvg_eq_diagonal (Theta_isPrimitiveRoot (n + 1))
          (Nat.succ_ne_zero (n + 1)) (φ M)

end FourierAvg

@[expose] public section

/-! ## General (arbitrary n) Jensen's Operator Inequality -/

variable [PartialOrder A] [StarOrderedRing A]
variable {f : ℝ → ℝ} {I : Set ℝ}

/-- **Jensen's Operator Inequality** (Li–Wu 2012, Theorem 2.2, general n):

Let `A` be an ordered unital C⋆-algebra and `f : ℝ → ℝ` a continuous operator convex
function on a (not necessarily convex) set `I`.
Suppose:
1. `a : Fin (n+1) → A` are self-adjoint with `spectrum ℝ (a i) ⊆ I`.
2. `b : Fin (n+1) → A` satisfy `∑ i, star (b i) * b i = 1`.
Then:
`cfc f (∑ i, star (b i) * a i * b i) ≤ ∑ i, star (b i) * cfc f (a i) * b i`.
-/
theorem JensenOperator_convex_general
    {n : ℕ} {a b : Fin (n + 1) → A}
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : ∀ i, IsSelfAdjoint (a i))
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i = 1) :
    cfc f (∑ i, star (b i) * a i * b i) ≤
      ∑ i, star (b i) * cfc f (a i) * b i := by
  have hconv : ConvexOn ℝ {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} (cfc f) :=
    @hf_opconvex (Matrix (Fin (n + 1) ⊕ Unit) (Fin (n + 1) ⊕ Unit) A) _ _ _
  -- set ups
  let u := U b
  let v := fun k : Fin (n + 2) => V (A := A) k
  let X := fun a : (Fin (n + 1) → A) => star u * Diag a * u
  have hXa_conj : ∀ k, star (v k) * X a * v k ∈
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} := by
    refine fun k => ⟨?_, ?_⟩
    · exact Diag_isSelfAdjoint ha |>.conjugate' u |>.conjugate' (v k)
    · calc spectrum ℝ (star (v k) * X a * v k)
        = spectrum ℝ (X a):=
            Unitary.spectrum_star_left_conjugate (U := ⟨v k, V_mem_unitary k⟩)
      _ = spectrum ℝ (Diag a) :=
            Unitary.spectrum_star_left_conjugate (U := ⟨u, U_mem_unitary hb⟩)
      _ ⊆ I := Diag_spectrum_subset ha_spec
  have hXa_conj_sum : ∑ k, (1 / (↑(n + 2) : ℝ)) • (star (v k) * X a * v k) ∈
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ I} := by
    apply hconv.1.sum_mem
    · intro k _; positivity
    · simp; field_simp
    · exact fun k _ => hXa_conj k
  let ld := fun i => cfc f ((X a).diag i) -- LHS diag
  let rd := (X <| fun i => cfc f (a i)).diag -- RHS diag
  have ld_last : ld (Sum.inr ()) = cfc f (∑ i, star (b i) * a i * b i) := by
    unfold ld
    congr 1; exact StarU_Diag_U_last a b
  have rd_last : rd (Sum.inr ()) = ∑ i, star (b i) * cfc f (a i) * b i :=
    StarU_Diag_U_last (fun i => cfc f (a i)) b
  -- main assembly: ineq at last entry follows from ineq at entire diagonal
  suffices Matrix.diagonal ld ≤ Matrix.diagonal rd by
    rw [diagonal_le_diagonal_iff] at this
    exact ld_last ▸ rd_last ▸ this (Sum.inr ())
  -- helper
  have hcfc_push : ∀ k, cfc f (star (v k) * X a * v k)
      = star (v k) * X (fun i => cfc f (a i)) * v k := by
    intro k
    let U := u * v k
    have hU_mem : U ∈ unitary _ := mul_mem (U_mem_unitary hb) (V_mem_unitary k)
    calc cfc f (star (v k) * X a * v k)
      = cfc f ((star (v k) * star u) * Diag a * (u * v k)) := by grind only
    _ = cfc f (star U * Diag a * U) := by simp only [star_mul, U]
    _ = star U * cfc f (Diag a) * U :=
          CStarAlgebra.cfc_unitary_conj' (u := ⟨U, hU_mem⟩) (a := Diag a)
            (hf.mono (Diag_spectrum_subset ha_spec))
            (Diag_isSelfAdjoint ha)
            (Diag_isSelfAdjoint ha |>.conjugate' U)
    _ = (star (v k) * star u) * Diag (fun i => cfc f (a i)) * (u * v k) := by
          rw [star_mul, ← Diag_cfc_contI hf ha ha_spec]
    _ = star (v k) * X (fun i => cfc f (a i)) * v k := by
          simp only [X, mul_assoc]
  -- the main calc
  calc Matrix.diagonal ld
      = cfc f (Matrix.diagonal (X a).diag) := by
          symm; apply cfc_diagonal
          · rw [← MatCStar.spectrum_diagonal, ← V_avg_diag (X a)]
            exact hf.mono hXa_conj_sum.2
          · exact isSelfAdjoint_diagonal_iff.mp <| V_avg_diag (X a) ▸ hXa_conj_sum.1
    _ = cfc f (∑ k, (1 / (↑(n + 2) : ℝ)) • (star (v k) * X a * v k)) := by
          rw [V_avg_diag (X a)]
      -- apply convexity
    _ ≤ ∑ k, (1 / (↑(n + 2) : ℝ)) • cfc f (star (v k) * X a * v k) := by
          set_option backward.isDefEq.respectTransparency false in
          apply hconv.map_sum_le
          · intro k _; positivity
          · simp; field_simp
          · exact fun k _ => hXa_conj k
    _ = ∑ k, (1 / (↑(n + 2) : ℝ)) • (star (v k) * X (fun i => cfc f (a i)) * v k) := by
          simp_rw [hcfc_push]
    _ = Matrix.diagonal rd := by
          rw [V_avg_diag <| X <| fun i => cfc f (a i)]

/-- **Jensen's Operator Inequality, sub-unital version** (Li–Wu 2012, Corollary 2.4):

Same as `JensenOperator_convex_general` but with the weaker hypothesis
`∑ i, star (b i) * b i ≤ 1` and extra conditions `0 ∈ I` and `f 0 ≤ 0`.

Proof idea: extend to `n+1` elements with `b_{n+1} = (1 - ∑ b*b)^{1/2}` and `a_{n+1} = 0`,
apply the `= 1` version, then drop the last term using `f 0 ≤ 0`. -/
theorem JensenOperator_convex_general_sub
    {n : ℕ} {a b : Fin (n + 1) → A}
    (hI : 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : ∀ i, IsSelfAdjoint (a i))
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i ≤ 1) :
    cfc f (∑ i, star (b i) * a i * b i) ≤
      ∑ i, star (b i) * cfc f (a i) * b i := by
  -- define c = sqrt(1 - ∑ b*b) and collect its basic properties
  have h1mb_nonneg : 0 ≤ 1 - ∑ i, star (b i) * b i := sub_nonneg.mpr hb
  let c := CFC.sqrt (1 - ∑ i, star (b i) * b i)
  have hc_nonneg : 0 ≤ c := CFC.sqrt_nonneg _
  have hc_sa : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg hc_nonneg
  have hc_sq : star c * c = 1 - ∑ i, star (b i) * b i := by
    rw [hc_sa.star_eq]
    exact CFC.sqrt_mul_sqrt_self _
  -- extends `b`: b' = Fin.snoc b c satisfies ∑ star(b' i) * b' i = 1
  let b' : Fin (n + 2) → A := Fin.snoc b c
  have hb' : ∑ i, star (b' i) * b' i = 1 :=
    calc ∑ i, star (b' i) * b' i
        = ∑ i : Fin (n + 1), star (b' i.castSucc) * b' i.castSucc +
            star (b' (Fin.last _)) * b' (Fin.last _) := Fin.sum_univ_castSucc _
      _ = ∑ i, star (b i) * b i + star c * c := by
            simp only [b', Fin.snoc_castSucc, Fin.snoc_last]
      _ = 1 := by rw [hc_sq]; abel
  -- extends `a` by a zero entry
  let a' : Fin (n + 2) → A := Fin.snoc a 0
  have ha' : ∀ i, IsSelfAdjoint (a' i) :=
    fun i => i.lastCases (by simp [a']) (fun j => by simp [a', ha j])
  have ha'_spec : ∀ i, spectrum ℝ (a' i) ⊆ I :=
    fun i => i.lastCases
        (by
          unfold a'
          rcases subsingleton_or_nontrivial A <;> simp [hI])
        (fun j => by simp only [Fin.snoc_castSucc, ha_spec j, a'])
  -- final helper lemmas
  have lhs_eq : ∑ i, star (b' i) * a' i * b' i = ∑ i, star (b i) * a i * b i :=
    calc ∑ i, star (b' i) * a' i * b' i
        = ∑ i : Fin (n + 1), star (b' i.castSucc) * a' i.castSucc * b' i.castSucc
          + star (b' (Fin.last _)) * a' (Fin.last _) * b' (Fin.last _) :=
            Fin.sum_univ_castSucc _
      _ = ∑ i, star (b i) * a i * b i + star c * 0 * c := by
            simp only [a', b', Fin.snoc_castSucc, Fin.snoc_last]
      _ = ∑ i, star (b i) * a i * b i := by simp
  have last_term_le : star c * cfc f (0 : A) * c ≤ 0 :=
    calc star c * cfc f (0 : A) * c
        ≤ star c * 0 * c := by
            apply star_left_conjugate_le_conjugate
            rw [cfc_apply_zero, Algebra.algebraMap_eq_smul_one]
            exact smul_nonpos_of_nonpos_of_nonneg hf.2 zero_le_one
      _ = 0 := by simp
  -- the main step
  calc cfc f (∑ i, star (b i) * a i * b i)
      = cfc f (∑ i, star (b' i) * a' i * b' i) := by rw [lhs_eq]
      -- apply Jensen
    _ ≤ ∑ i, star (b' i) * cfc f (a' i) * b' i :=
          JensenOperator_convex_general hf.1 hf_opconvex ha' ha'_spec hb'
    _ = ∑ i, star (b i) * cfc f (a i) * b i + star c * cfc f (0 : A) * c := by
          rw [Fin.sum_univ_castSucc]
          simp only [a', b', Fin.snoc_castSucc, Fin.snoc_last]
    _ ≤ ∑ i, star (b i) * cfc f (a i) * b i := add_le_of_nonpos_right last_term_le

/-! ## n = 2 specializations -/

open Matrix Fin
variable {a₁ a₂ b₁ b₂ : A}

/-- Jensen's Operator Inequality, n = 2 case.
Specialization of `JensenOperator_convex_general` to two summands. -/
theorem JensenOperator_convex
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  have := JensenOperator_convex_general (n := 1) hf hf_opconvex
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (by intro i; fin_cases i <;> simp_all)
    (by intro i; fin_cases i <;> simp_all)
    (by simpa only [Nat.reduceAdd, sum_univ_two] using hb)
  simpa only [Nat.reduceAdd, sum_univ_two] using this

/-- Sub-unital Jensen's Operator Inequality, n = 2 case.
Specialization of `JensenOperator_convex_general_sub` to two summands. -/
theorem JensenOperator_convex_sub
    (hI : 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  have := JensenOperator_convex_general_sub hI hf hf_opconvex
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (by intro i; fin_cases i <;> simp_all)
    (by intro i; fin_cases i <;> simp_all)
    (by simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, sum_univ_two] using hb)
  simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, sum_univ_two] using this

/-! ## Concave versions -/

theorem JensenOperator_concave
    (hf : ContinuousOn f I) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  have h := JensenOperator_convex hf.neg
    (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave) ha ha_spec hb
  simp only [cfc_neg, mul_neg, neg_mul, ← neg_add] at h
  exact neg_le_neg_iff.mp h

theorem JensenOperator_concave_sub
    (hI : 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  have h := JensenOperator_convex_sub hI
    ⟨hf.1.neg, neg_nonpos.mpr hf.2⟩
    (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave) ha ha_spec hb
  simp only [cfc_neg, mul_neg, neg_mul, ← neg_add] at h
  exact neg_le_neg_iff.mp h

open Set

/-! ### Nonnegative versions

Versions apply to nonnegative elements of the C*-algebra,
which is useful for our application.
-/

theorem JensenOperator_convex_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ :=
  JensenOperator_convex_sub
    Set.self_mem_Ici
    hf
    hf_opconvex
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb

theorem JensenOperator_concave_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) :=
  JensenOperator_concave_sub
    Set.self_mem_Ici
    hf
    hf_opconcave
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb
