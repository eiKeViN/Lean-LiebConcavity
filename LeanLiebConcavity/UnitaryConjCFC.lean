import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# CFC commutes with unitary conjugation

## Section 1 — General

`conjStarAlgAut_map_cfc`, `cfc_unitary_conj`, `cfc_unitary_conj'` with minimal
typeclasses mirroring `StarAlgHom.map_cfc`. Continuity of the conjugation map
is an **explicit hypothesis** `hφ`.

## Section 2 — CStarAlgebra specialization

The same three results specialized to `[CStarAlgebra A]` with `S = ℂ`. Here
`hφ` is discharged automatically via `StarAlgEquiv.isometry`, so it does not
appear in the statement.
-/

/-! ### Section 1 — General -/

section General

variable {R S A : Type*} {p : A → Prop}
  [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [CommSemiring S] [Algebra R S]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [ContinuousFunctionalCalculus R A p] [ContinuousMap.UniqueHom R A]

include S in
/-- Conjugation by a unitary commutes with the continuous functional calculus.

Mirrors `StarAlgHom.map_cfc`: the `StarAlgEquiv` `Unitary.conjStarAlgAut S A u`
(which maps `x ↦ u * x * star u`) commutes with `cfc f`. Continuity of the conjugation
map is an explicit hypothesis. -/
theorem conjStarAlgAut_map_cfc (u : unitary A) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous (Unitary.conjStarAlgAut S A u))
    (ha : p a := by cfc_tac)
    (hφa : p ((Unitary.conjStarAlgAut S A u) a) := by cfc_tac) :
    (Unitary.conjStarAlgAut S A u) (cfc f a) = cfc f ((Unitary.conjStarAlgAut S A u) a) :=
  StarAlgHom.map_cfc (Unitary.conjStarAlgAut S A u : A →⋆ₐ[S] A) f a (hφ := hφ)

include S in
/-- Conjugation by a unitary commutes with CFC — explicit left-conjugation form:
`cfc f (↑u * a * star ↑u) = ↑u * cfc f a * star ↑u`. -/
theorem cfc_unitary_conj (u : unitary A) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous (Unitary.conjStarAlgAut S A u))
    (ha : p a := by cfc_tac)
    (hφa : p ((u : A) * a * star (u : A)) := by cfc_tac) :
    cfc f ((u : A) * a * star (u : A)) = (u : A) * cfc f a * star (u : A) := by
  have := conjStarAlgAut_map_cfc (S := S) u f a
      (hf := hf) (hφ := hφ) (ha := ha)
      (hφa := by rwa [Unitary.conjStarAlgAut_apply])
  simpa only [Unitary.conjStarAlgAut_apply] using this.symm

include S in
/-- Conjugation by a unitary commutes with CFC — explicit right-conjugation form:
`cfc f (star ↑u * a * ↑u) = star ↑u * cfc f a * ↑u`. -/
theorem cfc_unitary_conj' (u : unitary A) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous (Unitary.conjStarAlgAut S A (star u)))
    (ha : p a := by cfc_tac)
    (hφa : p (star (u : A) * a * (u : A)) := by cfc_tac) :
    cfc f (star (u : A) * a * (u : A)) = star (u : A) * cfc f a * (u : A) := by
  have := conjStarAlgAut_map_cfc (S := S) (star u) f a
      (hf := hf) (hφ := hφ) (ha := ha)
      (hφa := by rwa [Unitary.conjStarAlgAut_star_apply])
  simpa only [Unitary.conjStarAlgAut_star_apply] using this.symm

end General

/-! ### Section 2 — CStarAlgebra specialization -/

section CStarAlgebra

variable {A : Type*} {p : A → Prop} [CStarAlgebra A]

private lemma conjStarAlgAut_continuous' (u : unitary A) :
    Continuous (Unitary.conjStarAlgAut ℂ A u) :=
  (StarAlgEquiv.isometry (Unitary.conjStarAlgAut ℂ A u)).continuous

variable [ContinuousFunctionalCalculus ℝ A p]

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by a unitary commutes with the CFC on a `CStarAlgebra`.

Specialization of `conjStarAlgAut_map_cfc` to `S = ℂ`; continuity is automatic. -/
theorem CStarAlgebra.conjStarAlgAut_map_cfc (u : unitary A) (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac)
    (hφa : p ((Unitary.conjStarAlgAut ℂ A u) a) := by cfc_tac) :
    (Unitary.conjStarAlgAut ℂ A u) (cfc f a) = cfc f ((Unitary.conjStarAlgAut ℂ A u) a) :=
  _root_.conjStarAlgAut_map_cfc u f a (hφ := conjStarAlgAut_continuous' u)

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by a unitary commutes with CFC on a `CStarAlgebra` — left form:
`cfc f (u * a * star u) = u * cfc f a * star u`. Continuity is automatic. -/
theorem CStarAlgebra.cfc_unitary_conj {u : unitary A} {f : ℝ → ℝ} {a : A}
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac)
    (hφa : p ((u : A) * a * star (u : A)) := by cfc_tac) :
    cfc f ((u : A) * a * star (u : A)) = (u : A) * cfc f a * star (u : A) :=
  _root_.cfc_unitary_conj u f a (hφ := conjStarAlgAut_continuous' u)

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by a unitary commutes with CFC on a `CStarAlgebra` — right form:
`cfc f (star u * a * u) = star u * cfc f a * u`. Continuity is automatic. -/
theorem CStarAlgebra.cfc_unitary_conj' {u : unitary A} {f : ℝ → ℝ} {a : A}
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac)
    (hφa : p (star (u : A) * a * (u : A)) := by cfc_tac) :
    cfc f (star (u : A) * a * (u : A)) = star (u : A) * cfc f a * (u : A) :=
  _root_.cfc_unitary_conj' u f a (hφ := conjStarAlgAut_continuous' (star u))

end CStarAlgebra
