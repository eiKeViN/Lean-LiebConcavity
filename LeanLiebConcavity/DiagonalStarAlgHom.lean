import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Topology.Instances.Matrix

/-!
# `Matrix.diagonal` as a star algebra homomorphism

`Matrix.diagonalAlgHom` exists in Mathlib but is only an `AlgHom`.
Here we upgrade it to a `StarAlgHom` using `Matrix.diagonal_conjTranspose`.

This is a candidate for upstream contribution to Mathlib.

## C⋆-algebra instances on `Matrix n n A` — namespace `MatCStar`

`CStarMatrix n n A` is defined as `Matrix n n A` (via `Equiv.refl`), so `inferInstanceAs`
transfers its norm and algebra instances to `Matrix n n A`. These are registered as
`scoped instance`s inside the `MatCStar` namespace to avoid a norm diamond with
`MatrixSpecialization` (Frobenius norm) when `A` is `RCLike`. Callers activate them with
`open MatCStar`.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {α : Type*} [Semiring α]

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

/-- `Matrix.diagonalStarAlgHom` is continuous (the topology on `Matrix n n α` is the product
topology, and `Continuous.matrix_diagonal` is tagged `@[fun_prop]`). -/
theorem diagonalStarAlgHom_continuous [TopologicalSpace α] [ContinuousAdd α] :
    Continuous (diagonalStarAlgHom R (n := n) (α := α)) := by
  change Continuous (diagonal (α := α))
  exact continuous_id.matrix_diagonal

end StarAlgHom

section Invertible

/-- `IsUnit (diagonal d) ↔ ∀ i, IsUnit (d i)` for matrices over a (possibly non-commutative)
ring. Note: `Matrix.isUnit_diagonal` in Mathlib requires `CommRing`, so we need a separate proof.
The key: if `diagonal d * M = 1` then `M` must have `M i i = (d i)⁻¹`. -/
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

end Matrix

/-!
## `MatCStar` namespace

Open with `open MatCStar` to activate C⋆-algebra instances on `Matrix n n A`
(operator norm, CFC) without polluting the global instance graph.
-/

noncomputable section

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

scoped instance instCFCComplex : ContinuousFunctionalCalculus ℂ (Matrix n n A) IsStarNormal :=
  inferInstance

scoped instance instCFCReal : ContinuousFunctionalCalculus ℝ (Matrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

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
lemma isSelfAdjoint_diagonal {d : n → A} (hd : ∀ i, IsSelfAdjoint (d i)) :
    IsSelfAdjoint (Matrix.diagonal d) := by
  rwa [← Matrix.isHermitian_iff_isSelfAdjoint, Matrix.isHermitian_diagonal_iff]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Specialization of `isSelfAdjoint_diagonal` to the `Sum.elim` form used in `liWuDiag`. -/
lemma isSelfAdjoint_diagonal_sum_elim {m : ℕ} {a : Fin m → A} {c : A}
    (hsa : ∀ i, IsSelfAdjoint (a i)) (hsc : IsSelfAdjoint c) :
    IsSelfAdjoint (Matrix.diagonal (Sum.elim a (fun _ => c) : Fin m ⊕ Unit → A)) :=
  isSelfAdjoint_diagonal (fun i => i.casesOn hsa (fun _ => hsc))

/-- `Matrix.diagonalStarAlgHom` commutes with CFC. -/
theorem Matrix.diagonalStarAlgHom_map_cfc {f : ℝ → ℝ} {d : n → A}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i)))
    (hd : ∀ i, IsSelfAdjoint (d i)) :
    Matrix.diagonalStarAlgHom ℝ (cfc f d) = cfc f (Matrix.diagonalStarAlgHom ℝ d) :=
  (Matrix.diagonalStarAlgHom ℝ).map_cfc f d
    (Pi.spectrum_eq (R := ℝ) (κ := fun _ => A) d ▸ hf)
    (Matrix.diagonalStarAlgHom_continuous ℝ)
    (Pi.isSelfAdjoint.mpr hd)
    (isSelfAdjoint_diagonal hd)

/-- `Matrix.diagonal` commutes with CFC:
`diagonal (cfc f d) = cfc f (diagonal d)`. -/
theorem Matrix.diagonal_map_cfc {f : ℝ → ℝ} {d : n → A}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i)))
    (hd : ∀ i, IsSelfAdjoint (d i)) :
    Matrix.diagonal (cfc f d) = cfc f (Matrix.diagonal d) := by
  simpa only [Matrix.diagonalStarAlgHom_apply] using
    Matrix.diagonalStarAlgHom_map_cfc hf hd

/-- CFC acts entry-wise on `Matrix.diagonal`:
`cfc f (diagonal d) = diagonal (fun i => cfc f (d i))`. -/
lemma cfc_diagonal {f : ℝ → ℝ} {d : n → A}
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i)))
    (hd : ∀ i, IsSelfAdjoint (d i)) :
    cfc f (Matrix.diagonal d) = Matrix.diagonal (fun i => cfc f (d i)) := by
  rw [← Matrix.diagonal_map_cfc hf hd,
      cfc_map_pi (S := ℝ) f d hf (Pi.isSelfAdjoint.mpr hd) hd]

-- `Matrix.isUnit_diagonal_iff` is proved in the `Matrix.Invertible` section above.

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

end MatCStar

end
