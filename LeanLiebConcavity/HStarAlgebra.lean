import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# H*-algebra (Ambrose 1945)

An **H*-algebra** is a Hilbert space `H` over `𝕜` equipped with a compatible ⋆-semiring
structure satisfying `⟪a * x, y⟫ = ⟪x, a⋆ * y⟫` for all `a, x, y : H`.

## Main definitions

- `HStarAlgebra`: typeclass extending `InnerProductSpace 𝕜 H`, `Semiring H`, `StarRing H`
  with the H*-algebra axiom.
- `HStarAlgebra.Lmul`: left multiplication `a ↦ Lₐ : H →L[𝕜] H`.
- `HStarAlgebra.Rmul`: right multiplication `b ↦ Rᵦ : H →L[𝕜] H`.

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

/-- An **H*-algebra** (Ambrose 1945): an inner product space over `𝕜` with semiring and
star structure, satisfying `⟪a * x, y⟫ = ⟪x, a⋆ * y⟫` and `⟪x * a, y⟫ = ⟪x, y * a⋆⟫`. -/
class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] extends
    NormedAddCommGroup H, Semiring H, Algebra 𝕜 H, InnerProductSpace 𝕜 H, StarRing H where
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

variable [IsTopologicalSemiring H]

/-- Left multiplication as an algebra homomorphism `H →ₐ[𝕜] (H →L[𝕜] H)`.
The primary algebraic object; `Lmul` is derived from this.

We build the underlying `LinearMap` directly (rather than via `Algebra.lmul`) to
avoid the module diamond between `Algebra.toModule` and `InnerProductSpace.toModule`. -/
noncomputable def lmulAlgHom : H →ₐ[𝕜] (H →L[𝕜] H) where
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

/-! ### Right multiplication as CLM -/

/-- bundle right multiplication by `b` as a continuous linear map `H →L[𝕜] H`. -/
def Rmul (b : H) : H →L[𝕜] H where
  toLinearMap := LinearMap.mulRight 𝕜 b
  cont := continuous_mul_const b

@[simp]
theorem Rmul_apply {b x : H} : Rmul 𝕜 b x = x * b := rfl

@[simp]
theorem Rmul_zero : Rmul 𝕜 (0 : H) = (0 : H →L[𝕜] H) := by ext; simp

@[simp]
theorem Rmul_one : Rmul 𝕜 (1 : H) = (1 : H →L[𝕜] H) := by ext; simp

@[simp]
theorem Rmul_add {a b : H} : Rmul 𝕜 a + Rmul 𝕜 b = Rmul 𝕜 (a + b):= by
  ext; simp [mul_add]

-- Note: `Rmul` is an *anti*-homomorphism: `R_{ab} = R_b ∘ R_a`.
theorem Rmul_mul {a b : H} : Rmul 𝕜 b * Rmul 𝕜 a = Rmul 𝕜 (a * b) := by
  ext; simp [Rmul, mul_assoc]

@[simp]
theorem inner_Rmul_left (a x y : H) :
    ⟪(Rmul 𝕜 a) x, y⟫ = ⟪x, (Rmul 𝕜 (star a)) y⟫ :=
  by simp_rw [Rmul_apply, inner_mul_left_eq]

@[simp]
theorem inner_Rmul_right (a x y : H) :
    ⟪x, (Rmul 𝕜 a) y⟫ = ⟪(Rmul 𝕜 (star a)) x, y⟫ :=
  by simp_rw [Rmul_apply, inner_mul_right_eq]
/-! ### Commutativity of L and R -/

/-- Left and right multiplication operators commute: `Lₐ ∘ Rᵦ = Rᵦ ∘ Lₐ`,
i.e., `a * (x * b) = (a * x) * b`. -/
theorem Lmul_Rmul_comm (a b : H) : Lmul 𝕜 a * Rmul 𝕜 b = Rmul 𝕜 b * Lmul 𝕜 a := by
  ext; simp [mul_assoc]

/-- right multiplication via composing left multiplication with star -/
theorem Rmul_eq_star_Lmul_star (a : H) : Rmul 𝕜 a = star ∘ Lmul 𝕜 (star a) ∘ star := by
  ext x; simp

/-! ### Invertibility

If `a` is a unit in `H`, then `Lₐ` and `Rₐ` are units in `H →L[𝕜] H`.
-/

theorem Lmul_isUnit {a : H} (ha : IsUnit a) : IsUnit (Lmul 𝕜 a) := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨⟨Lmul 𝕜 ↑u, Lmul 𝕜 ↑u⁻¹, by simp [Lmul_mul], by simp [Lmul_mul]⟩, rfl⟩

theorem Rmul_isUnit {b : H} (hb : IsUnit b) : IsUnit (Rmul 𝕜 b) := by
  obtain ⟨u, rfl⟩ := hb
  -- Rmul is an anti-hom: Rmul (a*b) = Rmul b * Rmul a
  exact ⟨⟨Rmul 𝕜 ↑u, Rmul 𝕜 ↑u⁻¹, by simp [Rmul_mul], by simp [Rmul_mul]⟩, rfl⟩


/-! ### Symmetry of Lmul (no CompleteSpace needed) -/

/-- If `a` is self-adjoint, then left multiplication by `a` is a symmetric
operator: `⟪Lₐ x, y⟫ = ⟪x, Lₐ y⟫`. -/
theorem Lmul_isSymmetric {a : H} (ha : IsSelfAdjoint a) :
    LinearMap.IsSymmetric (Lmul 𝕜 a).toLinearMap :=
  fun x y => by simp [inner_Lmul_left, ha.star_eq]

/-- For any `s : H`, left multiplication by `s⋆ * s` has nonneg inner product:
`0 ≤ re ⟪L_{s⋆s} x, x⟫`. This is the base case for `Lmul_isPositive`. -/
theorem re_inner_Lmul_star_mul_self_nonneg (s x : H) :
    0 ≤ RCLike.re ⟪(Lmul 𝕜 (star s * s)) x, x⟫ := by
  simp_rw [Lmul_apply, mul_assoc, <- inner_right_mul_eq]
  exact inner_self_nonneg

/-! ### `Lmul` as a star algebra homomorphism (requires `CompleteSpace`) -/

section StarAlgHom
variable [CompleteSpace H]

/-- Left multiplication sends `star a` to the adjoint of `Lmul a`.
Proof: by `eq_adjoint_iff`, reduce to `⟪(star a) * x, y⟫ = ⟪x, a * y⟫`,
which is exactly the H*-algebra axiom `inner_left_mul_eq`. -/
theorem Lmul_star (a : H) :
    Lmul 𝕜 (star a) = star (Lmul 𝕜 a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    simp only [Lmul_apply, inner_left_mul_eq, star_star]

/-- Left multiplication as a star algebra homomorphism `H →⋆ₐ[𝕜] (H →L[𝕜] H)`. -/
noncomputable def lmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H) :=
  { lmulAlgHom 𝕜 with
    map_star' := Lmul_star 𝕜 }

variable {H : Type*} [PartialOrder H] [Ring H] [StarRing H] [StarOrderedRing H]

/-- Every nonneg element decomposes as `star s * s`. Requires CFC or StarOrderedRing axioms. -/
lemma nonneg_decompose {a : H} (ha : 0 ≤ a) : ∃ s, a = star s * s := by
  sorry

/-- If `0 ≤ a` in a `StarOrderedRing`, then `Lₐ` is a positive operator. -/
theorem Lmul_isPositive {a : H} (ha : 0 ≤ a) : (Lmul 𝕜 a).IsPositive := by
  constructor
  · exact Lmul_isSymmetric 𝕜 (IsSelfAdjoint.of_nonneg ha)
  · intro x
    rw [StarOrderedRing.nonneg_iff] at ha
    refine AddSubmonoid.closure_induction ha ?_ ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact re_inner_Lmul_star_mul_self_nonneg 𝕜 s x
    · simp
    · intro a b _ _ iha ihb
      simp only [map_add, ContinuousLinearMap.add_apply, inner_add_left, map_add]
      exact add_nonneg iha ihb

end StarAlgHom

end HStarAlgebra

/-! ## Typeclass audit

Temporarily check which instances resolve for the `StarAlgHom.map_cfc` setup.
Delete this section after the audit.
-/
section TypeclassAudit
variable (𝕜 : Type*) [RCLike 𝕜]
variable (H : Type*) [HStarAlgebra 𝕜 H]
variable [Algebra 𝕜 H] [IsTopologicalSemiring H] [CompleteSpace H]

-- Domain H: basic algebra
#check (inferInstance : Semiring H)
#check (inferInstance : StarRing H)
#check (inferInstance : TopologicalSpace H)
#check (inferInstance : Algebra 𝕜 H)
#check (inferInstance : Star H)

-- Intermediate: does H have NormedAddCommGroup and NormedSpace?
#check (inferInstance : InnerProductSpace 𝕜 H)
#check (inferInstance : NormedAddCommGroup H)
#check (inferInstance : NormedSpace 𝕜 H)

-- Codomain H →L[𝕜] H: ring and algebra
#check (inferInstance : Semiring (H →L[𝕜] H))
#check (inferInstance : NormedAddCommGroup (H →L[𝕜] H))
#check (inferInstance : NormedAlgebra 𝕜 (H →L[𝕜] H))
#check (inferInstance : Algebra 𝕜 (H →L[𝕜] H))
#check (inferInstance : Star (H →L[𝕜] H))
#check (inferInstance : StarRing (H →L[𝕜] H))

-- For map_cfc: scalar tower with ℝ
-- These FAIL — need explicit [IsScalarTower ℝ 𝕜 H] variable in CFC section:
-- #check (inferInstance : Algebra ℝ H)          -- fails (no SMul ℝ H)
-- #check (inferInstance : IsScalarTower ℝ 𝕜 H)  -- fails
-- #check (inferInstance : IsScalarTower ℝ 𝕜 (H →L[𝕜] H))  -- fails

end TypeclassAudit
