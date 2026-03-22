# Phase A: HilbertMatrix Type and Inner Product Structure

## Problem: Two-Norm Conflict

`Matrix (Fin n) (Fin n) ℂ` needs **two different norms** in this project:

1. **Operator norm** (for C\*-algebra structure, CFC on A and B)
   - Obtained via `toEuclideanCLM : Matrix ≃⋆ₐ CLM`
   - Satisfies C\*-property: `‖A† A‖ = ‖A‖²`
   - Activated by `open scoped Matrix.Norms.L2Operator`

2. **Trace inner product norm** (Frobenius norm, for Hilbert space structure)
   - Defined as `⟪X, Y⟫ = Tr(X† Y)` with `‖X‖² = ⟪X, X⟫`
   - Does **NOT** satisfy C\*-property
   - Provided by `Matrix.toMatrixInnerProductSpace 1 PosDef.one`

**Key fact**: These cannot coexist on the same type. Putting both on `Matrix` would create instance diamonds, and the norms are incompatible (Frobenius norm is much larger than operator norm for most matrices).

## Solution: Opaque Type Alias

Define `HilbertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ` as an opaque type alias. This allows:
- `Matrix` to keep the operator norm via `L2Operator` scope
- `HilbertMatrix` to have the trace inner product norm
- Explicit `Equiv.refl` to convert between them without computational cost

### Declaration Sketch

```lean
-- Opaque type alias (keeps Matrix and HilbertMatrix separate at type-level)
def HilbertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

-- Identity equivalence at data level
def hilbertMatrixEquiv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ HilbertMatrix n :=
  Equiv.refl _

-- Instances for HilbertMatrix: NormedAddCommGroup via trace inner product
noncomputable instance : NormedAddCommGroup (HilbertMatrix n) :=
  (1 : Matrix (Fin n) (Fin n) ℂ).toMatrixNormedAddCommGroup Matrix.PosDef.one

noncomputable instance : InnerProductSpace ℂ (HilbertMatrix n) :=
  (1 : Matrix (Fin n) (Fin n) ℂ).toMatrixInnerProductSpace Matrix.PosDef.one.posSemidef

noncomputable instance : CompleteSpace (HilbertMatrix n) :=
  -- Automatic: finite-dimensional subspace of `(Fin n → ℂ) →L[ℂ] (Fin n → ℂ)`
```

### Algebra Structure Transfer

Since `HilbertMatrix n := Matrix ...` (a `def`, not a wrapper type), Lean sees them as definitionally equal **at the computational level**. However, at the **type level** they are distinct, which prevents norm diamonds.

Transfer `Ring`, `StarRing`, `Algebra ℂ`, `Module ℂ` via:
```lean
instance : Ring (HilbertMatrix n) := inferInstance -- via Equiv
instance : StarRing (HilbertMatrix n) := inferInstance
instance : Algebra ℂ (HilbertMatrix n) := inferInstance
-- etc.
```

Or explicitly via `Equiv.semiringCongr`, `Equiv.starRingCongr`, etc., if needed to avoid typeclass search delays.

## Key Mathlib Components

### 1. Trace Inner Product via PosDef

**File**: `Analysis/Matrix/Order.lean:362–394`

```lean
-- Assuming M : Matrix n n 𝕜 with M.PosDef
noncomputable def Matrix.toMatrixNormedAddCommGroup
    (M : Matrix n n 𝕜) (hM : M.PosDef) : NormedAddCommGroup (Matrix n n 𝕜)
```

This defines:
- Inner product: `⟪x, y⟫ = Tr(y * M * x†)` (matrix adjoint, not type-level star)
- Norm: `‖x‖ = √⟪x, x⟫ = √Tr(x† * M * x)`
- Metric from the norm

With `M = 1` (identity):
```
⟪x, y⟫ = Tr(y * 1 * x†) = Tr(y x†) = Tr(x† y)  ✓ (trace inner product)
```

### 2. InnerProductSpace from PosSemidef

**File**: `Analysis/Matrix/Order.lean` (follows the NormedAddCommGroup section)

```lean
noncomputable def Matrix.toMatrixInnerProductSpace
    (M : Matrix n n 𝕜) (hM : M.PosSemidef) : InnerProductSpace 𝕜 (Matrix n n 𝕜)
```

Extends `toMatrixNormedAddCommGroup` with the conjugate-symmetry and Pythagorean law axioms.

**Why PosSemidef instead of PosDef?** Inner products only require nonnegative definiteness; positive definiteness is overkill. But for our purposes, `M = 1` is both PosDef and PosSemidef, so this distinction is academic.

### 3. Identity is PosDef

**File**: `LinearAlgebra/Matrix/PosDef.lean:204`

```lean
theorem Matrix.PosDef.one : PosDef (1 : Matrix n n ℝ)
```

Provides the proof that the identity matrix is positive definite. This is the lynchpin: it lets us write
```lean
Matrix.PosDef.one.posSemidef : PosSemidef (1 : Matrix (Fin n) (Fin n) ℂ)
```
and feed it to `toMatrixInnerProductSpace`.

### 4. L2 Operator Norm Instances (for Matrix only, not HilbertMatrix)

**File**: `Analysis/CStarAlgebra/Matrix.lean:89–295`

When you `open scoped Matrix.Norms.L2Operator`, the instances
- `instL2OpNormedAddCommGroup`, `instL2OpNormedRing`, `instL2OpNormedAlgebra`

become available on `Matrix n n 𝕜`, giving it the operator norm via the equivalence
```
Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)
```

This makes `Matrix` a C\*-algebra. **Do NOT apply this to `HilbertMatrix`** — it would conflict with the trace norm.

**Scope activation** (line 175):
```lean
open scoped Matrix.Norms.L2Operator
```

### 5. Star is Conjugate Transpose

**Not a separate Mathlib entry, but fundamental:**

In both `Matrix` and `HilbertMatrix`, `star` means conjugate transpose:
```
star A = Aᴴ = fun (i j) => conj (A j i)
```

This is defined in `Algebra/Star/Basic.lean` and is **independent of the norm** — it's a purely algebraic operation.

## Phase A Deliverables

1. **`HilbertMatrix` type definition** — opaque alias
2. **`hilbertMatrixEquiv`** — identity equivalence
3. **`NormedAddCommGroup (HilbertMatrix n)` instance** — via `toMatrixNormedAddCommGroup 1 PosDef.one`
4. **`InnerProductSpace ℂ (HilbertMatrix n)` instance** — via `toMatrixInnerProductSpace 1 PosDef.one.posSemidef`
5. **`CompleteSpace (HilbertMatrix n)` instance** — automatic (finite-dimensional)
6. **Algebra structure transfer**: `Ring`, `StarRing`, `Algebra ℂ`, `Module ℂ` on `HilbertMatrix n`
7. **Key lemma**: `inner_eq_trace : ⟪X, Y⟫_ℂ = Tr(star X * Y)` (or equivalent)

## Gotchas & Traps

1. **Instance search on Equiv-transferred instances can be slow** — if typeclass diamonds arise, fall back to explicit construction with `@[simp]` lemmas.

2. **`CompleteSpace` must be inferred carefully** — `HilbertMatrix n` is finite-dimensional (subspace of a finite-dimensional Hilbert space), so completeness is automatic, but Lean may not find it without guidance.

3. **Scope activation needed for Matrix instances** — If you're working with `Matrix` (not `HilbertMatrix`) and need CFC/CStarAlgebra, ensure `open scoped Matrix.Norms.L2Operator` is in scope.

4. **Star on HilbertMatrix is conjugate transpose, not adjoint** — At the type level, `HilbertMatrix n` doesn't know about the inner product, so `star` is still `Aᴴ`. The adjoint of `L_A : HilbertMatrix → HilbertMatrix` (as an endomorphism) is **defined via the inner product**, not via star on HilbertMatrix itself. This matters when constructing `lmulStarAlgHom` in Phase B.

5. **Avoid mixing Matrix and HilbertMatrix in the same proof** — Convert at the boundary using `hilbertMatrixEquiv`.

## Related Sections in Future Phases

- **Phase B (MulOperators.lean)**: `lmulStarAlgHom` uses `HilbertMatrix n →L[ℂ] HilbertMatrix n` and its `CStarAlgebra` structure
- **Phase C (MulOperators.lean)**: `rmul` conjugation trick relies on `star : HilbertMatrix → HilbertMatrix` being conjugate transpose
- **Phase D (Lieb.lean)**: `trace_identity` converts between `Matrix` (for A, B, K) and `HilbertMatrix` (for operator-level evaluation)
