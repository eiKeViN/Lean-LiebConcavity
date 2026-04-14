module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import LeanLiebConcavity.ForMathlib.ContinuousFunctionalCalculus.Unital

/-!
# `Matrix.diagonal` as a star algebra homomorphism

`Matrix.diagonalAlgHom` exists in Mathlib but is only an `AlgHom`.
Here we upgrade it to a `StarAlgHom`.

## C⋆-algebra instances on `Matrix n n A` — namespace `MatCStar`

`CStarMatrix n n A` is definitionally equal to `Matrix n n A`, so `inferInstanceAs`
transfers its norm and algebra instances to `Matrix n n A`.

These are registered scoped inside the `MatCStar` namespace to avoid a norm diamond with
`FrobeniusMat` (Frobenius norm) when `A` is `RCLike`.
Callers activate them with `open MatCStar`.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {α : Type*} [Semiring α]

section Invertible

/-- `IsUnit (diagonal d) ↔ ∀ i, IsUnit (d i)` for matrices over a (possibly non-commutative)
ring. This generalizes `Matrix.isUnit_diagonal` in Mathlib which requires `CommRing`. -/
theorem isUnit_diagonal_iff {d : n → α} :
    IsUnit (diagonal d) ↔ ∀ i, IsUnit (d i) := by
  constructor
  · intro ⟨u, hu⟩ i
    have hli := congr_fun (congr_fun u.mul_inv i) i
    have hri := congr_fun (congr_fun u.inv_mul i) i
    simp_rw [hu, mul_apply, diagonal_apply, one_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hli
    simp_rw [hu, mul_apply, diagonal_apply, one_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hri
    exact ⟨⟨d i, u.inv i i, hli, hri⟩, rfl⟩
  · intro h
    refine ⟨⟨diagonal d, diagonal (fun i => (h i).unit.inv), ?_, ?_⟩, rfl⟩
    all_goals
    ext i j
    simp only [Units.inv_eq_val_inv, mul_diagonal, diagonal_apply, ite_mul,
      zero_mul, one_apply]
    split_ifs with hij
    · subst hij
      first | exact (h i).unit.mul_inv | exact (h i).unit.inv_mul
    · rfl

end Invertible

section StarAlgHom

variable (R : Type*) [CommSemiring R]
variable [StarRing α] [Algebra R α]

/-- `Matrix.diagonal` as a `StarAlgHom`. -/
def diagonalStarAlgHom : StarAlgHom R (n → α) (Matrix n n α) :=
  { diagonalAlgHom R with
    map_star' := fun v => by simp [star_eq_conjTranspose, diagonal_conjTranspose] }

@[simp]
theorem diagonalStarAlgHom_apply (v : n → α) :
    diagonalStarAlgHom R v = diagonal v := by simp [diagonalStarAlgHom]

/-- `Matrix.diagonalStarAlgHom` is continuous -/
theorem diagonalStarAlgHom_continuous [TopologicalSpace α] [ContinuousAdd α] :
    Continuous (diagonalStarAlgHom R (n := n) (α := α)) := by
  change Continuous (diagonal (α := α))
  exact continuous_id.matrix_diagonal

end StarAlgHom

end Matrix


noncomputable section

/-!
## `MatCStar` namespace

Open with `open MatCStar` to activate C⋆-algebra instances on `Matrix n n A`
(operator norm, CFC) by borrowing from CStarMatrix without polluting the global instance.

TODO : replaces ℝ and ℂ and `IsSelfAdjoint` by more general type
-/

namespace MatCStar

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- Operator norm instances transferred from `CStarMatrix n n A`
scoped instance instNormedRing : NormedRing (Matrix n n A) :=
  inferInstanceAs (NormedRing (CStarMatrix n n A))

scoped instance instNormedAlgebra : NormedAlgebra ℂ (Matrix n n A) :=
  inferInstanceAs (NormedAlgebra ℂ (CStarMatrix n n A))

scoped instance instCStarAlgebra : CStarAlgebra (Matrix n n A) :=
  inferInstanceAs (CStarAlgebra (CStarMatrix n n A))

scoped instance instPartialOrder : PartialOrder (Matrix n n A) :=
  inferInstanceAs (PartialOrder (CStarMatrix n n A))

scoped instance instStarOrderedRing : StarOrderedRing (Matrix n n A) :=
  inferInstanceAs (StarOrderedRing (CStarMatrix n n A))

scoped instance instCFCReal : ContinuousFunctionalCalculus ℝ (Matrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

scoped instance instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n A) :=
  CStarAlgebra.instNonnegSpectrumClass

set_option linter.unusedFintypeInType false in
scoped instance instPiCFCComplex :
    ContinuousFunctionalCalculus ℂ (n → A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

set_option linter.unusedFintypeInType false in
scoped instance instPiCFCReal :
    ContinuousFunctionalCalculus ℝ (n → A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

omit [Fintype n] [PartialOrder A] [StarOrderedRing A] in
/-- A diagonal matrix is self-adjoint iff all its diagonal entries are self-adjoint. -/
theorem isSelfAdjoint_diagonal_iff {d : n → A} :
    IsSelfAdjoint (Matrix.diagonal d) ↔ ∀ i, IsSelfAdjoint (d i) := by
  rw [← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_diagonal_iff]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Specialization of `isSelfAdjoint_diagonal` to the `Sum.elim` form used in `liWuDiag`. -/
theorem isSelfAdjoint_diagonal_sum_elim {m : ℕ} {a : Fin m → A} {c : A}
    (hsa : ∀ i, IsSelfAdjoint (a i)) (hsc : IsSelfAdjoint c) :
    IsSelfAdjoint (Matrix.diagonal (Sum.elim a (fun _ => c) : Fin m ⊕ Unit → A)) :=
  isSelfAdjoint_diagonal_iff.mpr (fun i => i.casesOn hsa (fun _ => hsc))

/-- `Matrix.diagonalStarAlgHom` commutes with CFC. -/
theorem Matrix.diagonalStarAlgHom_map_cfc {f : ℝ → ℝ} {d : n → A}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i)))
    (hd : ∀ i, IsSelfAdjoint (d i)) :
    Matrix.diagonalStarAlgHom ℝ (cfc f d) = cfc f (Matrix.diagonalStarAlgHom ℝ d) :=
  (Matrix.diagonalStarAlgHom ℝ).map_cfc f d
    (Pi.spectrum_eq (R := ℝ) (κ := fun _ => A) d ▸ hf)
    (Matrix.diagonalStarAlgHom_continuous ℝ)
    (Pi.isSelfAdjoint.mpr hd)
    (isSelfAdjoint_diagonal_iff.mpr hd)

/-- `Matrix.diagonal` commutes with CFC:
`diagonal (cfc f d) = cfc f (diagonal d)`. -/
theorem Matrix.diagonal_map_cfc {f : ℝ → ℝ} {d : n → A}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i)))
    (hd : ∀ i, IsSelfAdjoint (d i)) :
    Matrix.diagonal (cfc f d) = cfc f (Matrix.diagonal d) := by
  simpa only [Matrix.diagonalStarAlgHom_apply] using
    Matrix.diagonalStarAlgHom_map_cfc hf hd

/-- CFC acts entry-wise on diagonal matrices:
`cfc f (diagonal d) = diagonal (fun i => cfc f (d i))`. -/
lemma cfc_diagonal {f : ℝ → ℝ} {d : n → A}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i)))
    (hd : ∀ i, IsSelfAdjoint (d i)) :
    cfc f (Matrix.diagonal d) = Matrix.diagonal (fun i => cfc f (d i)) := by
  rw [← Matrix.diagonal_map_cfc hf hd,
      cfc_map_pi (S := ℝ) f d hf (Pi.isSelfAdjoint.mpr hd) hd]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The spectrum of a diagonal matrix equals the union of the spectra of its entries. -/
theorem spectrum_diagonal (d : n → A) :
    spectrum ℝ (Matrix.diagonal d) = ⋃ i, spectrum ℝ (d i) := by
  ext r
  simp only [spectrum.mem_iff, Set.mem_iUnion]
  rw [show algebraMap ℝ (Matrix n n A) r = Matrix.diagonal (fun _ => algebraMap ℝ A r) by
    simp [Matrix.algebraMap_eq_diagonal]]
  simp only [show Matrix.diagonal (fun _ => algebraMap ℝ A r) - Matrix.diagonal d =
      Matrix.diagonal (fun i => algebraMap ℝ A r - d i) by simp [Matrix.diagonal_sub],
    Matrix.isUnit_diagonal_iff]
  push_neg
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The spectrum of a diagonal matrix is contained in `I` when each entry's spectrum is. -/
theorem spectrum_diagonal_subset {d : n → A} {I : Set ℝ}
    (h : ∀ i, spectrum ℝ (d i) ⊆ I) :
    spectrum ℝ (Matrix.diagonal d) ⊆ I := by
  rw [spectrum_diagonal]
  exact Set.iUnion_subset h

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal matrix over a C⋆-algebra is nonneg iff all its diagonal entries are nonneg. -/
theorem nonneg_diagonal_iff {d : n → A} :
    0 ≤ Matrix.diagonal d ↔ ∀ i, 0 ≤ d i := by
  constructor
  · intro h i
    obtain ⟨hsa, hspec⟩ := (nonneg_iff_sa_spectrum_nonneg).mp h
    rw [Matrix.isHermitian_iff_isSelfAdjoint.symm, Matrix.isHermitian_diagonal_iff] at hsa
    refine nonneg_iff_sa_spectrum_nonneg.mpr ⟨hsa i, fun x hx => hspec x ?_⟩
    exact spectrum_diagonal d ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
  · intro h
    refine nonneg_iff_sa_spectrum_nonneg.mpr
      ⟨isSelfAdjoint_diagonal_iff.mpr <| fun i => (nonneg_iff_sa_spectrum_nonneg.mp <| h i).1, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp <| (spectrum_diagonal d).symm ▸ hx
    exact (nonneg_iff_sa_spectrum_nonneg.mp <| h i).2 x hi

/-- (Star) ordering of diagonal matrices is entry-wise. -/
theorem diagonal_le_diagonal_iff {d e : n → A} :
    Matrix.diagonal d ≤ Matrix.diagonal e ↔ ∀ i, d i ≤ e i := by
  rw [← sub_nonneg, Matrix.diagonal_sub, nonneg_diagonal_iff]
  simp_rw [sub_nonneg]

end MatCStar

end
