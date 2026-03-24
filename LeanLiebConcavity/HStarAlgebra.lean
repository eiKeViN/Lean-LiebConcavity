import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

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
star structure, satisfying `⟪a * x, y⟫ = ⟪x, a⋆ * y⟫`. -/
class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [SeminormedAddCommGroup H] extends
    Semiring H, StarRing H, InnerProductSpace 𝕜 H where
  /-- The H*-algebra axiom: left multiplication by `a` is adjoint to
  left multiplication by `star a`. -/
  inner_mul_left {a x y : H} : inner (a * x) y = inner x (star a * y)

namespace HStarAlgebra

variable (𝕜 : Type*)
variable {H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup H] [HStarAlgebra 𝕜 H]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 H _ x y

/-! ### Inner product identities

The H*-algebra axiom and its derived forms. These are the key identities for
the adjoint calculation `Lmul (star a) = adjoint (Lmul a)`.
-/

@[simp]
theorem inner_mul_left_eq {a x y : H} :
    ⟪a * x, y⟫ = ⟪x, star a * y⟫ :=
  HStarAlgebra.inner_mul_left

@[simp]
theorem inner_mul_right_eq {a x y : H} :
    ⟪x, a * y⟫ = ⟪star a * x, y⟫ := by
  simp

/-! ### Left multiplication as CLM -/

variable [Algebra 𝕜 H] [IsTopologicalSemiring H]

/-- bundle left multiplication by `a` as a continuous linear map `H →L[𝕜] H`. -/
def Lmul (a : H) : H →L[𝕜] H where
  toLinearMap := Algebra.lmul 𝕜 H a
  cont := continuous_const_mul a

@[simp]
theorem Lmul_apply (a x : H) : (Lmul 𝕜 a) x = a * x := rfl

@[simp]
theorem Lmul_zero : Lmul 𝕜 0 = (0 : H →L[𝕜] H) := by ext; simp

@[simp]
theorem Lmul_one : Lmul 𝕜 1 = (1 : H →L[𝕜] H) := by ext; simp

@[simp]
theorem Lmul_add (a b : H) : Lmul 𝕜 (a + b) = (Lmul 𝕜 a) + (Lmul 𝕜 b) := by
  ext; simp [Lmul]

-- `*` on `H →L[𝕜] H` is composition, so this says `L_{ab} = Lₐ ∘ L_b`.
@[simp]
theorem Lmul_mul (a b : H) : Lmul 𝕜 (a * b) = Lmul 𝕜 a * Lmul 𝕜 b := by
  ext; simp [mul_assoc]

@[simp]
theorem Lmul_smul (k : 𝕜) (a : H) : Lmul 𝕜 (k • a) = k • Lmul 𝕜 a := by
  ext; simp

/-- The H*-algebra axiom in operator form: `⟪Lₐ x, y⟫ = ⟪x, L_{a⋆} y⟫`. -/
@[simp]
theorem inner_Lmul_left (a x y : H) :
    ⟪(Lmul 𝕜 a) x, y⟫ = ⟪x, (Lmul 𝕜 (star a)) y⟫ :=
  by simp_rw [Lmul_apply, inner_mul_left_eq]

/-- Adjoint form: `⟪x, Lₐ y⟫ = ⟪L_{a⋆} x, y⟫`. -/
@[simp]
theorem inner_Lmul_right (a x y : H) :
    ⟪x, (Lmul 𝕜 a) y⟫ = ⟪(Lmul 𝕜 (star a)) x, y⟫ :=
  by simp_rw [Lmul_apply, inner_mul_right_eq]

/-! ### Right multiplication as CLM -/

/-- bundle right multiplication by `b` as a continuous linear map `H →L[𝕜] H`. -/
def Rmul (b : H) : H →L[𝕜] H where
  toLinearMap := LinearMap.mulRight 𝕜 b
  cont := continuous_mul_const b

@[simp]
theorem Rmul_apply (b x : H) : Rmul 𝕜 b x = x * b := rfl

@[simp]
theorem Rmul_zero : Rmul 𝕜 (0 : H) = (0 : H →L[𝕜] H) := by ext; simp

@[simp]
theorem Rmul_one : Rmul 𝕜 (1 : H) = (1 : H →L[𝕜] H) := by ext; simp

@[simp]
theorem Rmul_add (a b : H) : Rmul 𝕜 (a + b) = Rmul 𝕜 a + Rmul 𝕜 b := by
  ext; simp [mul_add]

-- Note: `Rmul` is an *anti*-homomorphism: `R_{ab} = R_b ∘ R_a`.
theorem Rmul_mul (a b : H) : Rmul 𝕜 (a * b) = Rmul 𝕜 b * Rmul 𝕜 a := by
  ext; simp [Rmul, mul_assoc]

/-! ### Commutativity of L and R -/

/-- Left and right multiplication operators commute: `Lₐ ∘ Rᵦ = Rᵦ ∘ Lₐ`,
i.e., `a * (x * b) = (a * x) * b`. -/
theorem Lmul_Rmul_comm (a b : H) : Lmul 𝕜 a * Rmul 𝕜 b = Rmul 𝕜 b * Lmul 𝕜 a := by
  ext; simp [mul_assoc]

/-- right multiplication via composing left multiplication with star -/
theorem Rmul_eq_star_Lmul_star (a : H) : Rmul 𝕜 a = star ∘ Lmul 𝕜 (star a) ∘ star := by
  ext x; simp

/-! ## Star-algebra homomorphism (stub)

The eventual goal is to package `Lmul` as a `StarAlgHom`:

```
def lmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H)
```

The algebraic fields (`map_zero'`, `map_add'`, `map_one'`, `map_mul'`) follow
from `Lmul_zero`, `Lmul_add`, `Lmul_one`, `Lmul_mul` above.

The `commutes'` field needs `Algebra 𝕜 (H →L[𝕜] H)` and the identity
`Lmul (algebraMap 𝕜 H c) = algebraMap 𝕜 (H →L[𝕜] H) c`, which reduces to
`(c • 1) * x = c • x` via `Algebra.algebraMap_eq_smul_one`.

The key `map_star'` field needs `[CompleteSpace H]` (for `adjoint`) and proves
`Lmul (star a) = adjoint (Lmul a)` via `inner_Lmul_left` + `adjoint_inner_left`
+ `ext_inner_right`.
-/

#check (H →L[𝕜] H)

set_option trace.Meta.synthInstance true
variable {A : Type*} [Ring A] [PartialOrder A] [TopologicalSpace A]
[StarRing A] [StarOrderedRing A] [Algebra ℂ A]
[ContinuousFunctionalCalculus ℂ A IsStarNormal]
[SeminormedAddCommGroup A] [HStarAlgebra ℂ A]

#check A

end HStarAlgebra
