module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The star-conjugation map `a ↦ op(star a)` as a `StarAlgEquiv ℝ A Aᵐᵒᵖ`

The map `x ↦ op(star x)` is `starRingEquiv : A ≃+* Aᵐᵒᵖ`.
Here we promote it to a star-algebra equivalence `starAlgEquiv`, then introduce a
downstream abbreviation `opStar` analogous to `Lmul`/`Rmul` in `HStarAlgebra`.

## Main definitions

- `starAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ` — the star-algebra equiv `a ↦ op(star a)`
- `opStar a : Aᵐᵒᵖ` — the downstream abbrev, equal to `op (star a)`

## API

- `opStar_apply`, `opStar_zero`, `opStar_one`, `opStar_add`, `opStar_mul`, `opStar_star`
- `opStar_isSelfAdjoint`, `opStar_nonneg` (under `[PartialOrder A] [StarOrderedRing A]`)
- `opStar_map_cfc` — CFC commutativity: `opStar (cfc f a) = cfc f (opStar a)`
- `opStar_rpow_nonneg` — rpow commutativity: `(opStar a)^r = opStar (a^r)`
- `op_rpow_eq_rpow_op` — corollary: `(op a)^r = op (a^r)` for nonneg `a`, `r`
-/
@[expose] public section

set_option linter.unusedSectionVars true

open MulOpposite

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]


/-! ### The star-algebra equivalence -/

/-- The map `a ↦ op(star a)` as a star-algebra equivalence `A ≃⋆ₐ[ℝ] Aᵐᵒᵖ`. -/
@[simps! apply]
def starAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ :=
  { starRingEquiv with
    map_smul' := fun r x => by simp [starRingEquiv, star_smul, TrivialStar.star_trivial]
    map_star' := fun x => by simp [starRingEquiv, op_star] }

/-! ### Downstream abbreviation `opStar` -/

/-- The map `a ↦ op(star a)`, star-conjugation into the opposite algebra. -/
abbrev opStar (a : A) : Aᵐᵒᵖ := starAlgEquiv a

@[simp] theorem opStar_apply (a : A) : opStar a = star (op a) := starAlgEquiv_apply a

@[simp] theorem opStar_zero : opStar (0 : A) = 0 :=
  map_zero starAlgEquiv

@[simp] theorem opStar_one : opStar (1 : A) = 1 :=
  map_one starAlgEquiv

@[simp] theorem opStar_add (a b : A) : opStar (a + b) = opStar a + opStar b :=
  map_add starAlgEquiv a b

@[simp] theorem opStar_mul (a b : A) : opStar (a * b) = opStar a * opStar b :=
  map_mul starAlgEquiv a b

@[simp] theorem opStar_star (a : A) : opStar (star a) = star (opStar a) :=
  map_star starAlgEquiv a

/-! ### Self-adjointness and nonnegativity -/

theorem opStar_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (opStar a) :=
  ha.map starAlgEquiv

section Nonneg

/-- For self-adjoint `a`, `opStar a = op a`. -/
theorem opStar_eq_op {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : opStar a = op a := by
  simp [← op_star, ha.star_eq]

variable [PartialOrder A] [StarOrderedRing A]
theorem opStar_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ opStar a :=
  opStar_eq_op (IsSelfAdjoint.of_nonneg ha) ▸ op_nonneg.mpr ha

end Nonneg

/-! ### Continuity -/

variable [TopologicalSpace A] [ContinuousStar A]

theorem opStar_continuous : Continuous (opStar : A → Aᵐᵒᵖ) :=
  continuous_op.comp continuous_star

/-! ### CFC commutativity: `opStar (cfc f a) = cfc f (opStar a)` -/

section MapCFC

variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]
variable [ContinuousMap.UniqueHom ℝ Aᵐᵒᵖ]

theorem starAlgEquiv_map_cfc (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    starAlgEquiv (cfc f a) = cfc f (starAlgEquiv a) :=
  StarAlgHomClass.map_cfc starAlgEquiv f a hf
    opStar_continuous ha (ha.map starAlgEquiv)

/-- CFC commutativity for `opStar`: `opStar (cfc f a) = cfc f (opStar a)`. -/
theorem opStar_map_cfc (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    opStar (cfc f a) = cfc f (opStar a) :=
  starAlgEquiv_map_cfc f a hf ha

end MapCFC

/-! ### rpow commutativity -/

private theorem rpow_continuousOn_pos {r : ℝ} : ContinuousOn (fun (x : ℝ) ↦ x ^ r) (Set.Ioi 0) :=
  continuousOn_id.rpow_const (by grind only [= Set.mem_Ioi, = id.eq_1])

section Rpow

variable [PartialOrder A] [StarOrderedRing A]
variable [T2Space A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]

/-- `opStar` commutes with nonneg real powers: `(opStar a)^r = opStar (a^r)`. -/
theorem opStar_rpow_nonneg' {a : A} {r : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    cfc (fun x : ℝ ↦ x ^ r) (opStar a : Aᵐᵒᵖ) = opStar (cfc (fun x : ℝ ↦ x ^ r) a) :=
  (opStar_map_cfc (· ^ r) a).symm

/-- `op` commutes with nonneg real powers (cfc form): `cfc (·^r) (op a) = op (cfc (·^r) a)`.
Follows from `opStar_rpow_nonneg'` since `opStar a = op a` for self-adjoint `a`. -/
theorem op_rpow_eq_rpow_op_nonneg' {a : A} {r : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    cfc (fun x : ℝ ↦ x ^ r) (op a : Aᵐᵒᵖ) = op (cfc (fun x : ℝ ↦ x ^ r) a) := by
  rw [← opStar_eq_op, ← opStar_eq_op]
  exact opStar_rpow_nonneg' hr

variable [NonnegSpectrumClass ℝ A]

/-- `opStar` commutes with real powers for strictly positive elements (cfc form). -/
theorem opStar_rpow_strictlyPositive'
    {a : A} {r : ℝ} (ha : IsStrictlyPositive a := by cfc_tac) :
    cfc (fun x : ℝ ↦ x ^ r) (opStar a : Aᵐᵒᵖ) = opStar (cfc (fun x : ℝ ↦ x ^ r) a) :=
  (opStar_map_cfc (· ^ r) a <|
    rpow_continuousOn_pos.mono <| fun _ hx => ha.spectrum_pos hx).symm

/-- `op` commutes with real powers for strictly positive elements (cfc form). -/
theorem op_rpow_eq_rpow_op'
    {a : A} {r : ℝ} (ha : IsStrictlyPositive a := by cfc_tac) :
    cfc (fun x : ℝ ↦ x ^ r) (op a : Aᵐᵒᵖ) = op (cfc (fun x : ℝ ↦ x ^ r) a) := by
  rw [← opStar_eq_op, ← opStar_eq_op]
  exact opStar_rpow_strictlyPositive'

variable [IsTopologicalRing A] [IsTopologicalRing Aᵐᵒᵖ] [NonnegSpectrumClass ℝ Aᵐᵒᵖ]

/-- `op` commutes with nonneg real powers: `(op a)^r = op (a^r)`. -/
theorem op_rpow_eq_rpow_op_nonneg {a : A} {r : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (op a : Aᵐᵒᵖ) ^ r = op (a ^ r) := by
  rw [CFC.rpow_eq_cfc_real, CFC.rpow_eq_cfc_real]
  exact op_rpow_eq_rpow_op_nonneg' hr

/-- `op` commutes with real powers for `a` strictly positive. -/
theorem op_rpow_eq_rpow_op {a : A} {r : ℝ} (ha : IsStrictlyPositive a := by cfc_tac) :
    (op a : Aᵐᵒᵖ) ^ r = op (a ^ r) := by
  rw [CFC.rpow_eq_cfc_real, CFC.rpow_eq_cfc_real]
  exact op_rpow_eq_rpow_op'

end Rpow
