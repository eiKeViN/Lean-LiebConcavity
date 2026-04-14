module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import LeanLiebConcavity.ForMathlib.Continuity

/-!
# The star-conjugation map `a ↦ op(star a)` as a `StarAlgEquiv R A Aᵐᵒᵖ`

The map `x ↦ op(star x)` is `starRingEquiv : A ≃+* Aᵐᵒᵖ`.
Here we promote it to a star-algebra equivalence `starAlgEquiv`,
in order to interact with continuous functional calculus.

## Main definitions

- `starAlgEquiv : A ≃⋆ₐ[R] Aᵐᵒᵖ` — the star-algebra equiv `a ↦ op(star a)`
- `opStar a : Aᵐᵒᵖ` — the downstream abbrev, equal to `op (star a)`

## Main results
- `opStar_map_cfc` — CFC commutativity: `opStar (cfc f a) = cfc f (opStar a)`
- `op_rpow_eq_nonneg` — `(op a)^r = op (a^r)` for nonneg `a`, `r`
- `op_rpow_eq_strictpos` — `(op a)^r = op (a^r)` for strictly positive `a`
-/

@[expose] public section

open MulOpposite

variable {A : Type*}

/-- abbrev of `op ∘ star` with no extra structure. -/
abbrev opStar [Star A] (a : A) : Aᵐᵒᵖ := op (star a)

@[simp] theorem opStar_apply [Star A] (a : A) :
    opStar a = star (op a) := op_star a |>.symm

@[simp] theorem opStar_star [Star A] (a : A) :
    opStar (star a) = star (opStar a) := by
  simp [op_star]

@[simp] theorem opStar_one [MulOneClass A] [StarMul A] :
    opStar (1 : A) = 1 := by
  simp [star_one]

@[simp] theorem opStar_zero [AddMonoid A] [StarAddMonoid A] :
    opStar (0 : A) = 0 := by simp

@[simp] theorem opStar_add [AddMonoid A] [StarAddMonoid A] (a b : A) :
    opStar (a + b) = opStar a + opStar b := by
  simp [star_add]

@[simp] theorem opStar_mul [Mul A] [StarMul A] (a b : A) :
    opStar (a * b) = opStar a * opStar b := by
  simp [star_mul]

/-! ## opStar as star-algebra equivalence -/

section StarAlgEquiv

variable (R : Type*) [CommSemiring R] [StarRing R] [TrivialStar R]
variable [Ring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- The map `a ↦ op(star a)` as a star-algebra equivalence `A ≃⋆ₐ[R] Aᵐᵒᵖ`. -/
@[simps! apply]
def starAlgEquiv : A ≃⋆ₐ[R] Aᵐᵒᵖ :=
  { starRingEquiv with
    map_smul' := fun r x => by simp [starRingEquiv, star_smul, TrivialStar.star_trivial]
    map_star' := fun x => by simp [starRingEquiv, op_star] }

/-- `opStar` is toFun of `starAlgEquiv`. -/
@[simp] theorem opStar_eq_starAlgEquiv (a : A) : opStar a = starAlgEquiv R a := rfl

end StarAlgEquiv

/-! ## Self-adjointness and nonnegativity -/

section Nonneg

theorem opStar_isSelfAdjoint [Star A] {a : A} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (opStar a) := by
  dsimp [IsSelfAdjoint]; simp_rw [← op_star, ha.star_eq]

/-- For self-adjoint `a`, `opStar a = op a`. -/
theorem opStar_eq_op [Star A] {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    opStar a = op a := by
  simp [← op_star, ha.star_eq]

theorem opStar_nonneg [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha : 0 ≤ a) : 0 ≤ opStar a :=
  opStar_eq_op (IsSelfAdjoint.of_nonneg ha) ▸ op_nonneg.mpr ha

end Nonneg


/-! ## Continuity -/

section Continuity

theorem opStar_continuous [Star A] [TopologicalSpace A] [ContinuousStar A] :
    Continuous (opStar : A → Aᵐᵒᵖ) :=
  continuous_op.comp continuous_star

end Continuity


/-! ## CFC commutativity -/

section CFC

variable {R : Type*} [CommSemiring R] [StarRing R] [TrivialStar R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Ring A] [StarRing A] [TopologicalSpace A] [ContinuousStar A]
variable [Algebra R A] [StarModule R A]
    [ContinuousFunctionalCalculus R A IsSelfAdjoint]
    [ContinuousFunctionalCalculus R Aᵐᵒᵖ IsSelfAdjoint]
    [ContinuousMap.UniqueHom R Aᵐᵒᵖ]

theorem starAlgEquiv_map_cfc (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    starAlgEquiv R (cfc f a) = cfc f (starAlgEquiv R a) :=
  StarAlgHomClass.map_cfc (starAlgEquiv R) f a hf
    opStar_continuous ha (ha.map (starAlgEquiv R))

/-- CFC commutativity for `opStar`: `opStar (cfc f a) = cfc f (opStar a)`. -/
theorem opStar_map_cfc (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    opStar (cfc f a) = cfc f (opStar a) :=
  starAlgEquiv_map_cfc f a hf ha

end CFC

/-! ## rpow commutativity -/

section Rpow

variable {A : Type*} [Ring A] [StarRing A]
    [Algebra ℝ A] [StarModule ℝ A]
    [TopologicalSpace A] [ContinuousStar A]
    [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]
    [ContinuousMap.UniqueHom ℝ Aᵐᵒᵖ]

/-- `opStar` commutes with nonneg real powers (cfc form): `(opStar a)^r = opStar (a^r)`. -/
theorem opStar_rpow_nonneg' {a : A} {r : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    cfc (fun x : ℝ ↦ x ^ r) (opStar a : Aᵐᵒᵖ) = opStar (cfc (fun x : ℝ ↦ x ^ r) a) :=
  (opStar_map_cfc (· ^ r) a).symm

/-- `op` commutes with nonneg real powers (cfc form): `cfc (·^r) (op a) = op (cfc (·^r) a)`. -/
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
theorem op_rpow_eq_rpow_op_strictlyPositive'
    {a : A} {r : ℝ} (ha : IsStrictlyPositive a := by cfc_tac) :
    cfc (fun x : ℝ ↦ x ^ r) (op a : Aᵐᵒᵖ) = op (cfc (fun x : ℝ ↦ x ^ r) a) := by
  rw [← opStar_eq_op, ← opStar_eq_op]
  exact opStar_rpow_strictlyPositive'

variable [T2Space A] [IsTopologicalRing A] [NonnegSpectrumClass ℝ Aᵐᵒᵖ]

/-- `op` commutes with nonneg real powers: `(op a)^r = op (a^r)`. -/
theorem op_rpow_eq_rpow_op_nonneg {a : A} {r : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (op a : Aᵐᵒᵖ) ^ r = op (a ^ r) := by
  rw [CFC.rpow_eq_cfc_real, CFC.rpow_eq_cfc_real]
  exact op_rpow_eq_rpow_op_nonneg' hr

/-- `op` commutes with real powers for `a` strictly positive. -/
theorem op_rpow_eq_rpow_op_strictlyPositive {a : A} {r : ℝ}
    (ha : IsStrictlyPositive a := by cfc_tac) :
    (op a : Aᵐᵒᵖ) ^ r = op (a ^ r) := by
  rw [CFC.rpow_eq_cfc_real, CFC.rpow_eq_cfc_real]
  exact op_rpow_eq_rpow_op_strictlyPositive'

end Rpow
