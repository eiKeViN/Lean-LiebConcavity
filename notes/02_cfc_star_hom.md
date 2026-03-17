# CFC Preservation Under Star-Algebra Homomorphisms, and `L_A^s = L_{A^s}`

## Mathematical statement

If `φ : A → B` is a continuous unital *-algebra homomorphism, `a ∈ A` is
self-adjoint, and `f ∈ C(spectrum ℝ a)`, then `φ(cfc f a) = cfc f (φ a)`.

---

## 1. Lean stubs for this project

These declarations belong in `LeanLiebConcavity/ForMathlib.lean`:

```lean
section LeftMulStarHom

variable {n : ℕ}

/-- Left multiplication by A is adjoint to left multiplication by A*
    with respect to the trace inner product: ⟨AX, Y⟩ = ⟨X, A*Y⟩. -/
-- [potential upstream contribution to Mathlib]
lemma mulLeft_adjoint_mulLeft_star (A : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((A * X) * star Y) = Matrix.trace (X * star (star A * Y)) := by
  sorry -- follows from Matrix.trace_mul_comm and star_mul

/-- L_A as a star algebra homomorphism into End(A) (Hilbert-Schmidt inner product). -/
-- NOTE: requires equipping End(Matrix n n ℂ) with the Hilbert-Schmidt star structure
noncomputable def lmulStarAlgHom : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] _ := by
  sorry

/-- L_A^s = L_{A^s} for nonneg real powers. -/
theorem rpow_mulLeft (A : Matrix (Fin n) (Fin n) ℂ) (hA : 0 ≤ A) (s : ℝ≥0) :
    mulLeft ℂ (A ^ (s : ℝ)) = (mulLeft ℂ A) ^ (s : ℝ) := by
  sorry -- apply StarAlgHom.map_cfc lmulStarAlgHom

/-- R_B^s = R_{B^s} for nonneg real powers. -/
theorem rpow_mulRight (B : Matrix (Fin n) (Fin n) ℂ) (hB : 0 ≤ B) (s : ℝ≥0) :
    mulRight ℂ (B ^ (s : ℝ)) = (mulRight ℂ B) ^ (s : ℝ) := by
  sorry -- reduce to rpow_mulLeft via R_B X = star (L_{B*} (star X))

end LeftMulStarHom
```

**What needs to be proved** (the non-sorry steps):

1. **`lmul_star`**: `mulLeft ℂ (star A) = star (mulLeft ℂ A)` in `B(A)` with
   Hilbert-Schmidt adjoint. Key computation: `⟨AX, Y⟩ = Tr((AX)*Y) = Tr(X*(A*Y)) = ⟨X, A*Y⟩`
   using `Matrix.trace_mul_comm`.
2. **`lmulStarAlgHom`**: package `Algebra.lmul` + `lmul_star` into a `StarAlgHom`.
3. **`rpow_mulLeft`**: apply `StarAlgHom.map_cfc lmulStarAlgHom` with `f = · ^ s`.
4. **`rpow_mulRight`**: use `R_B X = star (mulLeft ℂ (star B) (star X))`.

---

## 2. Core preservation theorem

### Unital CFC

```
Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean  (~line 483)

lemma StarAlgHomClass.map_cfc (φ : F) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous φ := by fun_prop)
    (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) :
    φ (cfc f a) = cfc f (φ a)

-- Explicit dot-notation version for φ : A →⋆ₐ[S] B:
lemma StarAlgHom.map_cfc (φ : A →⋆ₐ[S] B) (f : R → R) (a : A) ... :
    φ (cfc f a) = cfc f (φ a)
```

**Required typeclasses:**
- `[ContinuousFunctionalCalculus R A p]` and `[ContinuousFunctionalCalculus R B q]`
- `[ContinuousMap.UniqueHom R B]` — uniqueness of the CFC on `B` (holds for C*-algebras)
- `[AlgHomClass F S A B] [StarHomClass F A B]` and `Continuous φ`

**Proof idea:** both `φ ∘ cfcHom_a` and `cfcHom_{φ(a)}` are continuous
*-algebra homs `C(σ(a)) → B` agreeing on `id`, so they are equal by uniqueness.

### Non-unital CFC

```
-- Same file, ~line 434
lemma NonUnitalStarAlgHomClass.map_cfcₙ (φ : F) (f : R → R) (a : A)
    (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (hφ : Continuous φ := by fun_prop)
    (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) :
    φ (cfcₙ f a) = cfcₙ f (φ a)
```

---

## 3. Analysis: what Mathlib provides for `L_A`

### What exists

`Algebra.lmul` is an algebra homomorphism (not star):
```
Mathlib/Algebra/Algebra/Bilinear.lean  (line 137)
def Algebra.lmul : A →ₐ[R] End R A
```

Natural-number power identities:
```
-- lines 111–114
@[simp] theorem pow_mulLeft  (a : A) (n : ℕ) : mulLeft R a ^ n  = mulLeft R (a ^ n)
@[simp] theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n)
```
**These give `L_A^n = L_{A^n}` for `n : ℕ` for free.**

Continuous version:
```
Mathlib/Analysis/Normed/Operator/Mul.lean  (line 65)
def NonUnitalAlgHom.Lmul : R →ₙₐ[𝕜] R →L[𝕜] R
```

### What is missing

There is **no** `A →⋆ₐ[R] End R A` for `lmul` in Mathlib.
The gap is the star-algebra-hom property `L_{A*} = (L_A)*`, which requires:
1. A star structure on `End ℂ A` via the Hilbert-Schmidt adjoint.
2. The adjoint computation `⟨AX, Y⟩ = ⟨X, A*Y⟩`.

### Strategy for `R_B` (right multiplication)

`R_B : X ↦ X * B` is an *anti*-hom: `R_{B₁B₂} = R_{B₂} ∘ R_{B₁}`.

Two approaches:
- **`MulOpposite`:** treat `R_B` as a hom `A →ₐ[ℂ] (End ℂ A)ᵐᵒᵖ` using `starRingEquiv`.
- **Matrix trick:** `R_B X = star(mulLeft ℂ (star B)(star X))`, reducing to the left case.

The matrix trick is simplest in the matrix setting:
```
R_B X = X * B = star(B* * X*) = star(L_{B*}(star X))
```
so `R_B^s = star ∘ L_{B*}^s ∘ star = star ∘ L_{(B*)^s} ∘ star = R_{(B^s)}` (using `star B ^ s = (B^s)*` for `0 ≤ B`).

---

## 4. Summary of Mathlib infrastructure

| Result | File | Status |
|--------|------|--------|
| `Algebra.lmul : A →ₐ[R] End R A` | `Algebra/Algebra/Bilinear.lean` | ✓ |
| `pow_mulLeft : mulLeft R a ^ n = mulLeft R (a ^ n)` | `Algebra/Algebra/Bilinear.lean` | ✓ |
| `pow_mulRight : mulRight R a ^ n = mulRight R (a ^ n)` | `Algebra/Algebra/Bilinear.lean` | ✓ |
| `NonUnitalAlgHom.Lmul : R →ₙₐ[𝕜] R →L[𝕜] R` | `Analysis/Normed/Operator/Mul.lean` | ✓ |
| `StarRing Rᵐᵒᵖ` instance | `Algebra/Star/Basic.lean` | ✓ |
| `starRingEquiv : R ≃+* Rᵐᵒᵖ` | `Algebra/Star/Basic.lean` | ✓ |
| `StarAlgHom.map_cfc` | `CStarAlgebra/CFC/Unique.lean` | ✓ |
| `A →⋆ₐ[ℂ] End ℂ A` for `lmul` | — | ✗ missing |
| `(mulLeft ℂ A)† = mulLeft ℂ (star A)` | — | ✗ missing |

### Key files

| File | Content |
|------|---------|
| `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean` | `StarAlgHom.map_cfc`, `NonUnitalStarAlgHom.map_cfcₙ` |
| `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | `cfcHom`, its properties |
| `Analysis/CStarAlgebra/Hom.lean` | Spectrum preservation, isometry for *-homs |
| `Algebra/Algebra/Bilinear.lean` | `Algebra.lmul`, `pow_mulLeft`, `pow_mulRight` |
| `Algebra/Module/LinearMap/Basic.lean` | `LinearMap.mulLeft`, `mulLeft_mul` |
| `Analysis/Normed/Operator/Mul.lean` | `NonUnitalAlgHom.Lmul` (continuous version) |
| `Algebra/Star/Basic.lean` | `StarRing Rᵐᵒᵖ`, `starRingEquiv` |
