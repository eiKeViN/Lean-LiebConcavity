import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# H*-algebra (Ambrose 1945)

An **H*-algebra** is a Hilbert space `H` over `𝕜` equipped with a compatible ⋆-semiring
structure satisfying `⟪a * x, y⟫ = ⟪x, a⋆ * y⟫` for all `a, x, y : H`.
The induced norm makes it a normed ring: `‖x * y‖ ≤ ‖x‖ * ‖y‖` for all `x y : H`.

## Main definitions

- `HStarAlgebra`: typeclass extending `InnerProductSpace 𝕜 H`, `Semiring H`, `StarRing H`
  with the H*-algebra axiom.
- `HStarAlgebra.lmulStarAlgHom`: left multiplication as a star algebra homomorphism
  `H →⋆ₐ[𝕜] (H →L[𝕜] H)`.
- `HStarAlgebra.rmulStarAlgHom`: right multiplication as a star algebra homomorphism
  `H →⋆ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ`.

## Design note

The class uses `extends` (not mixin) to merge the `AddCommGroup H` diamond:
both `InnerProductSpace 𝕜 H` (via `NormedAddCommGroup`) and `Semiring H`
provide `AddCommGroup H`. The `extends` mechanism unifies them into a single
field, avoiding instance conflicts for abstract types.

## References

- Warren Ambrose, *Structure theorems for a special class of Banach algebras*,
  Trans. AMS 57 (1945), 364–386.
-/

noncomputable section

open scoped ComplexOrder

/-! ## Class definition -/

class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] extends
    NormedRing H, Algebra 𝕜 H, InnerProductSpace 𝕜 H, StarRing H where
  inner_mul_left {a x y : H} : inner (a * x) y = inner x (star a * y)
  inner_mul_right {a x y : H} : inner (x * a) y = inner x (y * star a)

export HStarAlgebra (inner_mul_left inner_mul_right)

namespace HStarAlgebra

variable (𝕜 : Type*)
variable {H : Type*} [RCLike 𝕜] [HStarAlgebra 𝕜 H]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 H _ x y

/-! ### Inner product identities

The H*-algebra axiom and its derived forms. These are the key identities for
the adjoint calculation `Lmul (star a) = adjoint (Lmul a)`.
-/

@[simp]
theorem inner_left_mul_eq {a x y : H} :
    ⟪a * x, y⟫ = ⟪x, star a * y⟫ :=
  inner_mul_left

@[simp]
theorem inner_right_mul_eq {a x y : H} :
    ⟪x, a * y⟫ = ⟪star a * x, y⟫ := by
  rw [inner_left_mul_eq, star_star]
@[simp]
theorem inner_mul_left_eq {a x y : H} :
    ⟪x * a, y⟫ = ⟪x, y * star a⟫ :=
  inner_mul_right

@[simp]
theorem inner_mul_right_eq {a x y : H} :
    ⟪x, y * a⟫ = ⟪x * star a, y⟫ := by
  rw [inner_mul_left_eq, star_star]

/-! ### Left multiplication as an algebra homomorphism -/

/-- Left multiplication as an algebra homomorphism `H →ₐ[𝕜] (H →L[𝕜] H)`.
The primary algebraic object; `Lmul` is derived from this.

We build the underlying `LinearMap` directly (rather than via `Algebra.lmul`) to
avoid the module diamond between `Algebra.toModule` and `InnerProductSpace.toModule`. -/
def lmulAlgHom : H →ₐ[𝕜] (H →L[𝕜] H) where
  toFun a :=
    { toFun    := (a * ·)
      map_add' := mul_add a
      map_smul' := fun c x => mul_smul_comm c a x
      cont     := continuous_const_mul a }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' := fun a b => by ext; simp [add_mul]
  commutes' := fun c => by ext; simp [Algebra.algebraMap_eq_smul_one]

/-- Left multiplication by `a`, as a continuous linear map `H →L[𝕜] H`. -/
abbrev Lmul (a : H) : H →L[𝕜] H := lmulAlgHom 𝕜 a

@[simp]
theorem Lmul_apply {a x : H} : Lmul 𝕜 a x = a * x := rfl

@[simp]
theorem Lmul_zero : Lmul 𝕜 0 = (0 : H →L[𝕜] H) := map_zero (lmulAlgHom 𝕜)

@[simp]
theorem Lmul_one : Lmul 𝕜 1 = (1 : H →L[𝕜] H) := map_one (lmulAlgHom 𝕜)

@[simp]
theorem Lmul_add {a b : H} : Lmul 𝕜 (a + b) = Lmul 𝕜 a + Lmul 𝕜 b :=
  map_add (lmulAlgHom 𝕜) a b

-- `*` on `H →L[𝕜] H` is composition, so this says `L_{ab} = Lₐ ∘ L_b`.
@[simp]
theorem Lmul_mul {a b : H} : Lmul 𝕜 (a * b) = Lmul 𝕜 a * Lmul 𝕜 b :=
  map_mul (lmulAlgHom 𝕜) a b

@[simp]
theorem Lmul_smul {k : 𝕜} {a : H} : k • Lmul 𝕜 a = Lmul 𝕜 (k • a) := by
  ext; simp

/-- The H*-algebra axiom in operator form: `⟪Lₐ x, y⟫ = ⟪x, L_{a⋆} y⟫`. -/
@[simp]
theorem inner_Lmul_left (a x y : H) :
    ⟪(Lmul 𝕜 a) x, y⟫ = ⟪x, (Lmul 𝕜 (star a)) y⟫ :=
  by simp_rw [Lmul_apply, inner_left_mul_eq]

@[simp]
theorem inner_Lmul_right (a x y : H) :
    ⟪x, (Lmul 𝕜 a) y⟫ = ⟪(Lmul 𝕜 (star a)) x, y⟫ :=
  by simp_rw [Lmul_apply, inner_right_mul_eq]

/-! ### Right multiplication as algebra homomorphism -/

open MulOpposite

/-- Right multiplication as an algebra homomorphism into the *opposite* operator algebra,
`H →ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ`, mapping `a ↦ op(Rₐ)`.

Since right multiplication is a ring *anti*-homomorphism on `H`
(`R_{ab} = R_b ∘ R_a`), it is a genuine ring homomorphism into `B(H)ᵐᵒᵖ`,
where multiplication is reversed: `op(Rₐ) * op(Rᵦ) = op(Rᵦ ∘ Rₐ) = op(R_{ab})`.

This mirrors `lmulAlgHom : H →ₐ[𝕜] (H →L[𝕜] H)`. -/
def rmulAlgHom : H →ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ where
  toFun a := op
    { toLinearMap := LinearMap.mulRight 𝕜 a
      cont        := continuous_mul_const a }
  map_one'   := by apply congrArg op; ext; simp
  map_mul' a b := by
    simp only [← op_mul]
    congr 1; ext x; simp [mul_assoc]
  map_zero'  := by apply congrArg op; ext; simp
  map_add' a b := by apply congrArg op; ext x; simp [mul_add]
  commutes' c  := by apply congrArg op; ext x; simp [Algebra.algebraMap_eq_smul_one]

/-- Right multiplication by `a`, as a continuous linear map `H →L[𝕜] H`. -/
abbrev Rmul (a : H) : H →L[𝕜] H := unop (rmulAlgHom 𝕜 a)

@[simp]
theorem Rmul_apply {a x : H} : Rmul 𝕜 a x = x * a := rfl

@[simp]
theorem Rmul_zero : Rmul 𝕜 0 = (0 : H →L[𝕜] H) :=
  op_injective (map_zero (rmulAlgHom 𝕜))

@[simp]
theorem Rmul_one : Rmul 𝕜 1 = (1 : H →L[𝕜] H) :=
  op_injective (map_one (rmulAlgHom 𝕜))

@[simp]
theorem Rmul_add {a b : H} : Rmul 𝕜 (a + b) = Rmul 𝕜 a + Rmul 𝕜 b :=
  op_injective (map_add (rmulAlgHom 𝕜) a b)

@[simp]
theorem Rmul_smul {k : 𝕜} {a : H} : k • Rmul 𝕜 a = Rmul 𝕜 (k • a) := by ext; simp

-- Note: `Rmul` is an *anti*-homomorphism: `R_{ab} = R_b ∘ R_a`.
theorem Rmul_mul {a b : H} : Rmul 𝕜 (a * b) = Rmul 𝕜 b * Rmul 𝕜 a :=
  op_injective (map_mul (rmulAlgHom 𝕜) a b)

@[simp]
theorem inner_Rmul_left (a x y : H) :
    ⟪(Rmul 𝕜 a) x, y⟫ = ⟪x, (Rmul 𝕜 (star a)) y⟫ :=
  by simp_rw [Rmul_apply, inner_mul_left_eq]

@[simp]
theorem inner_Rmul_right (a x y : H) :
    ⟪x, (Rmul 𝕜 a) y⟫ = ⟪(Rmul 𝕜 (star a)) x, y⟫ :=
  by simp_rw [Rmul_apply, inner_mul_right_eq]


/-! ### Commutativity of L and R

Left and right multiplication operators commute: `Lₐ ∘ Rᵦ = Rᵦ ∘ Lₐ`,
i.e., `a * (x * b) = (a * x) * b`.
-/

theorem Lmul_Rmul_comm (a b : H) : Lmul 𝕜 a * Rmul 𝕜 b = Rmul 𝕜 b * Lmul 𝕜 a := by
  ext; simp [mul_assoc]

/-- right multiplication via composing left multiplication with star -/
theorem Rmul_eq_star_Lmul_star (a : H) : Rmul 𝕜 a = star ∘ Lmul 𝕜 (star a) ∘ star := by
  ext x; simp


/-! ### Continuity of L and R as functions

Multiplication is a bounded bilinear map (by `isBoundedBilinearMap_mul`),
so its curried CLM `H →L[𝕜] H →L[𝕜] H` is automatically continuous.
-/

/-- The map `a ↦ Lₐ` and `a ↦ Rₐ` are continuous w.r.t. the operator norm -/
theorem lmulStarAlgHom_continuous :
    Continuous (fun a : H => Lmul 𝕜 a : H → H →L[𝕜] H) :=
  (isBoundedBilinearMap_mul (𝕜 := 𝕜) (A := H)).toContinuousLinearMap.continuous

/-- The map `a ↦ R_a` is continuous w.r.t. the operator norm -/
theorem rmulAlgHom_continuous :
    Continuous (fun a : H => Rmul 𝕜 a : H → H →L[𝕜] H) :=
  (ContinuousLinearMap.flip
    (isBoundedBilinearMap_mul (𝕜 := 𝕜) (A := H)).toContinuousLinearMap).continuous


/-! ### Invertibility preserving

If `a` is invertible, then `Lₐ` and `Rₐ` are invertible in `H →L[𝕜] H`.
-/

theorem Lmul_isUnit {a : H} (ha : IsUnit a) : IsUnit (Lmul 𝕜 a) := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨⟨Lmul 𝕜 ↑u, Lmul 𝕜 ↑u⁻¹, by simp [← Lmul_mul], by simp [← Lmul_mul]⟩, rfl⟩

theorem Rmul_isUnit {b : H} (hb : IsUnit b) : IsUnit (Rmul 𝕜 b) := by
  obtain ⟨u, rfl⟩ := hb
  exact ⟨⟨Rmul 𝕜 ↑u, Rmul 𝕜 ↑u⁻¹, by simp [← Rmul_mul], by simp [← Rmul_mul]⟩, rfl⟩


/-! ### Symmetry preserving

If `a` is self-adjoint, then `Lₐ` and `Rₐ` are symmetric operators:
`⟪Lₐ x, y⟫ = ⟪x, Lₐ y⟫` and `⟪Rₐ x, y⟫ = ⟪x, Rₐ y⟫`.
-/

theorem Lmul_isSymmetric {a : H} (ha : IsSelfAdjoint a) :
    LinearMap.IsSymmetric (Lmul 𝕜 a).toLinearMap :=
  fun x y => by
    change ⟪a * x, y⟫ = ⟪x, a * y⟫
    rw [inner_left_mul_eq, ha.star_eq]

theorem Rmul_isSymmetric {a : H} (ha : IsSelfAdjoint a) :
    LinearMap.IsSymmetric (Rmul 𝕜 a).toLinearMap :=
  fun x y => by
    change ⟪x * a, y⟫ = ⟪x, y * a⟫
    rw [inner_mul_left_eq, ha.star_eq]


section nonneg

/-! ### Nonnegativity preserving

left/right multiplication by nonnegative (semi-definite) elements are positive operators,
which are operators nonnegative with respect to the Loewner partial order.
-/

lemma re_inner_Lmul_star_mul_self_nonneg (s x : H) :
    0 ≤ RCLike.re ⟪(Lmul 𝕜 (star s * s)) x, x⟫ := by
  simp_rw [Lmul_apply, mul_assoc, <- inner_right_mul_eq]
  exact inner_self_nonneg

lemma re_inner_Rmul_star_mul_self_nonneg (s x : H) :
    0 ≤ RCLike.re ⟪(Rmul 𝕜 (star s * s)) x, x⟫ := by
  simp_rw [Rmul_apply, ← mul_assoc]
  rw [inner_mul_left_eq]
  exact inner_self_nonneg

variable [PartialOrder H] [StarOrderedRing H]
attribute [local instance] ContinuousLinearMap.instLoewnerPartialOrder

theorem Lmul_isPositive {a : H} (ha : 0 ≤ a) : (Lmul 𝕜 a).IsPositive := by
  refine ⟨Lmul_isSymmetric 𝕜 (IsSelfAdjoint.of_nonneg ha), fun x => ?_⟩
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      exact re_inner_Lmul_star_mul_self_nonneg 𝕜 s x
  | zero => simp
  | add b c _ _ ihb ihc =>
      rw [Lmul_add, ContinuousLinearMap.add_apply, inner_add_left, map_add RCLike.re]
      exact add_nonneg ihb ihc

theorem Rmul_isPositive {a : H} (ha : 0 ≤ a) : (Rmul 𝕜 a).IsPositive := by
  refine ⟨Rmul_isSymmetric 𝕜 (IsSelfAdjoint.of_nonneg ha), fun x => ?_⟩
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem b hb =>
      obtain ⟨s, rfl⟩ := hb
      exact re_inner_Rmul_star_mul_self_nonneg 𝕜 s x
  | zero => simp
  | add b c _ _ ihb ihc =>
      rw [Rmul_add, ContinuousLinearMap.add_apply, inner_add_left, map_add RCLike.re]
      exact add_nonneg ihb ihc

theorem Lmul_nonneg {a : H} (ha : 0 ≤ a) : 0 ≤ Lmul 𝕜 a := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive (Lmul 𝕜 a)]
  exact Lmul_isPositive 𝕜 ha

theorem Rmul_nonneg {a : H} (ha : 0 ≤ a) : 0 ≤ Rmul 𝕜 a := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive (Rmul 𝕜 a)]
  exact Rmul_isPositive 𝕜 ha

end nonneg


/-! ### `Lmul` and `Rmul` as star algebra homomorphisms (requires `CompleteSpace`)

Only with H complete, star/adjoint structure can be instantiated on `H →L[𝕜] H`.

Then left/right multiplication preserves stars (hence self-adjointness).
-/

section StarAlgHom
variable [CompleteSpace H]
-- notes: with H complete, star/adjoint structure can be instantiated on `H →L[𝕜] H`.

theorem Lmul_star (a : H) :
    Lmul 𝕜 (star a) = star (Lmul 𝕜 a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    simp only [Lmul_apply, inner_left_mul_eq, star_star]

theorem Rmul_star (a : H) :
    Rmul 𝕜 (star a) = star (Rmul 𝕜 a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    simp only [Rmul_apply, inner_mul_left_eq, star_star]

/-- Left multiplication as a star algebra homomorphism `H →⋆ₐ[𝕜] (H →L[𝕜] H)`. -/
def lmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H) :=
  { lmulAlgHom 𝕜 with
    map_star' := Lmul_star 𝕜 }

/-- Right multiplication as a star algebra homomorphism `H →⋆ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ`. -/
def rmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ :=
  { rmulAlgHom 𝕜 with
    map_star' := fun a => congrArg op (Rmul_star 𝕜 a) }

/-- If `a` is self-adjoint, then `Lₐ` is self-adjoint as an operator. -/
theorem Lmul_isSelfAdjoint {a : H} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (lmulStarAlgHom 𝕜 a) :=
  ha.map (lmulStarAlgHom 𝕜)

/-- If `a` is self-adjoint in `H`, then `Rₐ` is self-adjoint as an operator. -/
theorem Rmul_isSelfAdjoint {a : H} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (Rmul 𝕜 a) := by
  simp only [IsSelfAdjoint, ← Rmul_star, ha.star_eq]

end StarAlgHom


/-! ### CFC commutation: `L_{f(a)} = f(L_a)` -/

namespace CFC
open Set

-- could upgrade this a lemma to `ForMathlib`.
theorem rpow_continuousOn_pos {r : ℝ} : ContinuousOn (fun (x : ℝ) ↦ x ^ r) (Ioi 0) :=
    continuousOn_id.rpow_const (by grind only [= mem_Ioi, = id.eq_1])

variable [CompleteSpace H] [Algebra ℝ H] [IsScalarTower ℝ 𝕜 H]
variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
variable [ContinuousFunctionalCalculus ℝ H IsSelfAdjoint]
variable [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

/-- Left multiplication commutes with the continuous functional calculus:
`L_{f(a)} = f(L_a)` for self-adjoint `a` and continuous `f`. -/
theorem Lmul_map_cfc (f : ℝ → ℝ) (a : H)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    lmulStarAlgHom 𝕜 (cfc f a) = cfc f (lmulStarAlgHom 𝕜 a) :=
  (lmulStarAlgHom 𝕜).map_cfc _ _ hf (lmulStarAlgHom_continuous 𝕜) ha
    (Lmul_isSelfAdjoint 𝕜 ha)

variable [PartialOrder H] [StarOrderedRing H]
variable [StarOrderedRing (H →L[𝕜] H)]
variable [NonnegSpectrumClass ℝ H] [NonnegSpectrumClass ℝ (H →L[𝕜] H)]

/-- Left multiplication commutes with nonneg real powers: `(L_a)^r = L_{a^r}`. -/
theorem Lmul_rpow_nonneg {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (Lmul 𝕜 a) ^ r = Lmul 𝕜 (a ^ r)  := by
  symm
  rw [CFC.rpow_eq_cfc_real ha, CFC.rpow_eq_cfc_real <| Lmul_nonneg 𝕜 ha]
  exact Lmul_map_cfc 𝕜 (· ^ r) a

/-- need a version that applies to taking negative powers -/
theorem Lmul_rpow_strictlyPositive {r : ℝ} {a : H} (ha : IsStrictlyPositive a := by cfc_tac) :
    (Lmul 𝕜 a) ^ r = Lmul 𝕜 (a ^ r) := by
  symm
  rw [CFC.rpow_eq_cfc_real ha.nonneg, CFC.rpow_eq_cfc_real <| Lmul_nonneg 𝕜 ha.nonneg]
  refine Lmul_map_cfc 𝕜 (· ^ r) a <| rpow_continuousOn_pos.mono ?_
  exact fun _ hx => ha.spectrum_pos hx

theorem Lmul_rpow_nonneg_apply {r : ℝ} {a x : H}
    (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    ((Lmul 𝕜 a) ^ r) x = a ^ r * x := by
  rw [Lmul_rpow_nonneg 𝕜 hr]; simp

theorem Lmul_rpow_strictlyPositive_apply {r : ℝ} {a x : H}
    (ha : IsStrictlyPositive a := by cfc_tac) :
    ((Lmul 𝕜 a) ^ r) x = a ^ r * x := by
  rw [Lmul_rpow_strictlyPositive 𝕜]; simp

end CFC


end HStarAlgebra
