# C*-Algebra Homomorphisms Preserve Continuous Functional Calculus — Mathlib Survey

**Mathematical statement (PlanetMath):** If φ: A → B is a *-homomorphism of unital
C*-algebras, a ∈ A is normal, and f ∈ C(σ(a)), then φ(f(a)) = f(φ(a)).

---

## Part I: The Core Preservation Theorem

### `StarAlgHom.map_cfc` and `StarAlgHomClass.map_cfc`

**File:** `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean`
**Lines:** ~483–512

```lean
-- Generic version (via FunLike / AlgHomClass / StarHomClass)
lemma StarAlgHomClass.map_cfc (φ : F) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous φ := by fun_prop)
    (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) :
    φ (cfc f a) = cfc f (φ a)

-- Dot-notation wrapper for explicit star algebra homomorphisms φ : A →⋆ₐ[S] B
lemma StarAlgHom.map_cfc (φ : A →⋆ₐ[S] B) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hφ : Continuous φ := by fun_prop)
    (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) :
    φ (cfc f a) = cfc f (φ a)
```

**Required type-class context (abbreviated):**
- `[ContinuousFunctionalCalculus R A p]` and `[ContinuousFunctionalCalculus R B q]`
- `[ContinuousMap.UniqueHom R B]` (uniqueness of CFC on B — holds for C*-algebras)
- `[AlgHomClass F S A B] [StarHomClass F A B]` and `Continuous φ`

The proof strategy uses the *uniqueness* of the continuous functional calculus: both
`φ ∘ cfcHom_a` and `cfcHom_{φ(a)}` are continuous *-algebra homomorphisms
`C(σ(a), R) → B` agreeing on the identity function, hence they are equal.

### Non-Unital Parallel

For non-unital C*-algebras, the analogous results use `cfcₙ` (non-unital CFC):

```lean
lemma NonUnitalStarAlgHomClass.map_cfcₙ (φ : F) (f : R → R) (a : A)
    (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (hφ : Continuous φ := by fun_prop)
    (ha : p a := by cfc_tac)
    (hφa : q (φ a) := by cfc_tac) :
    φ (cfcₙ f a) = cfcₙ f (φ a)
```

**File:** same `Unique.lean`, lines ~434–464.

---

## Part II: L_A^s = L_{A^s} and R_B^s = R_{B^s}

### Goal

Let A be a C*-algebra. Define:
- `L_A : A →ₗ[ℂ] A` by `L_A X = A * X`  (left multiplication)
- `R_B : A →ₗ[ℂ] A` by `R_B X = X * B`  (right multiplication)

For `s : ℝ≥0` (or `s ∈ [0,1]`), using the CFC power `a ^ s` in the C*-algebra `A`,
the goal is to prove `L_A ^ s = L_{A^s}` and `R_B ^ s = R_{B^s}`,
where `^ s` on the left is the CFC power in `B(A)` (the C*-algebra of bounded
operators on `A`) and `^ s` on the right is the CFC power in `A`.

The strategy is:
1. **Step 1.** Show `A ↦ L_A` is a *-algebra homomorphism `A →⋆ₐ[ℂ] B(A)`.
2. **Step 2.** Apply `StarAlgHom.map_cfc` to `L_A` with `f(x) = x ^ s`.

---

### Step 1a: Left Multiplication — What Mathlib Already Has

**Algebra hom (no star):**

```lean
-- File: Mathlib/Algebra/Algebra/Bilinear.lean (lines 137–140)
def Algebra.lmul : A →ₐ[R] End R A
```
where `End R A = A →ₗ[R] A` is the endomorphism algebra.

This is a **unital algebra homomorphism** for any `[CommSemiring R] [Semiring A] [Algebra R A]`,
i.e., it satisfies:
- `lmul (a * b) = lmul a ∘ lmul b`  (multiplicativity)
- `lmul 1 = id`                       (unitality)
- `lmul` is `R`-linear              (linearity)

The multiplicativity is proved by `pow_mulLeft`:
```lean
-- File: Mathlib/Algebra/Algebra/Bilinear.lean (lines 111–114)
-- (also in Mathlib/Algebra/Module/LinearMap/Basic.lean as mulLeft_mul)
@[simp]
theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n)
```
Similarly:
```lean
@[simp]
theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n)
```

**These give `L_A^n = L_{A^n}` for natural number powers `n : ℕ` for free.**

The non-unital version:
```lean
-- File: Mathlib/Algebra/Algebra/Bilinear.lean (lines 76–79)
def NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A
```

Continuous version (for normed algebras):
```lean
-- File: Mathlib/Analysis/Normed/Operator/Mul.lean (lines 65–68)
def NonUnitalAlgHom.Lmul : R →ₙₐ[𝕜] R →L[𝕜] R
-- maps a to the continuous linear map (X ↦ a * X)
```

**What is missing:** There is **no** `A →⋆ₐ[R] End R A` for `lmul` in Mathlib in general.
The star algebra hom version requires equipping `End R A` with a star structure (the
Hilbert space adjoint) and verifying `lmul (star a) = star (lmul a)`, i.e.,
`L_{A*} = (L_A)*`.

---

### Step 1b: Proving `lmul` is a Star Algebra Homomorphism

The star-algebra-hom property `L_{A*} = (L_A)*` follows from the trace inner product
identity:
```
⟨L_A X, Y⟩ = Tr((AX) Y*) = Tr(X (A* Y)*) = ⟨X, L_{A*} Y⟩
```
so `(L_A)* = L_{A*}`.

**What this requires in Lean:**
1. A star structure on `End ℂ A` (or on `A →L[ℂ] A`) given by the Hilbert space adjoint
   with respect to the Hilbert-Schmidt / trace inner product on `A = Mₙ(ℂ)`.
2. A proof that `lmul (star a) = star (lmul a)` in this star algebra.

**Available generality:**
- For finite-dimensional C*-algebras (e.g. `Matrix (Fin n) (Fin n) ℂ`): the trace
  inner product is available via `Lean-QuantumInfo` (trace inner product, inner product
  space structure on matrices).
- For general C*-algebras: the GNS construction gives a Hilbert space on which `L_A`
  is a bounded operator; the adjoint condition holds by the C*-algebra axioms.
- **Lean-QuantumInfo** already provides matrix trace inner product infrastructure;
  the adjoint computation above can likely be proved using `Matrix.trace_mul_comm`.

**In the matrix case (`A = Matrix (Fin n) (Fin n) ℂ`):**
The inner product is `⟨X, Y⟩ = Tr(X* Y)` (or `Tr(X Y*)`). The adjoint calculation
becomes:
```lean
-- This can be proved using Matrix.trace_mul_comm and star_mul
-- ⟨A * X, Y⟩ = Tr((AX)* Y) = Tr(X* A* Y) = Tr(X* (A* Y)) = ⟨X, A* Y⟩
```
So `(mulLeft ℂ A)† = mulLeft ℂ (star A)` with respect to the Frobenius inner product.

---

### Step 1c: Right Multiplication — Anti-Homomorphism via MulOpposite

`R_B : X ↦ X * B` is an *anti*-homomorphism: `R_{B₁ * B₂} = R_{B₂} ∘ R_{B₁}`.

**The Mathlib approach:** Use `MulOpposite` (`Aᵐᵒᵖ`) to turn anti-homs into homs.

**Key fact from `Mathlib/Algebra/Star/Basic.lean` (lines 281–285):**
```lean
-- star as a ring equiv R → Rᵐᵒᵖ
def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ
-- toFun x = op (star x)
```

**Star structure on `MulOpposite` (from `Mathlib/Algebra/Star/Basic.lean`):**
```lean
instance [Star R] : Star Rᵐᵒᵖ where star r := op (star r.unop)
-- i.e., star (op r) = op (star r)
instance [NonUnitalSemiring R] [StarRing R] : StarRing Rᵐᵒᵖ where ...
```

**The right strategy for `R_B`:**

Define the anti-homomorphism of `A` as a homomorphism into `(End ℂ A)ᵐᵒᵖ`:
```lean
-- Conceptually:
def rmul : A →ₐ[ℂ] (End ℂ A)ᵐᵒᵖ
-- where rmul B = op (mulRight ℂ B)
```
Then `rmul (B₁ * B₂) = rmul B₁ * rmul B₂` (in `(End ℂ A)ᵐᵒᵖ`, multiplication is
reversed, which corrects for the anti-hom reversal of `mulRight`).

For the star property: `(R_B)* = R_{B*}` (same adjoint calculation as for `L_A`,
using `Tr((X B) Y*) = Tr(X (B Y*))`).

**Alternative: Use `starRingEquiv` directly.** Since `B ↦ op (star B)` is a ring hom
`A →+* Aᵐᵒᵖ`, and right multiplication by `B` in `A` equals left multiplication by
`op B` in `Aᵐᵒᵖ`, one can compose:
```
A →+* Aᵐᵒᵖ →ₐ[ℂ] End ℂ (Aᵐᵒᵖ)
B ↦  op B  ↦  (X ↦ op B * X)     [left mult in Aᵐᵒᵖ = right mult in A]
```
But the Hilbert space structure on `Aᵐᵒᵖ` vs `A` requires care.

**Simplest practical approach for the matrix case:** Note that in `Matrix (Fin n) (Fin n) ℂ`,
`R_B X = X * B = (B* * X*)* = star (mulLeft ℂ (star B) (star X))`, so
`R_B = star ∘ mulLeft ℂ (star B) ∘ star`. This reduces the right case to the left case.
The CFC power then follows from the left case applied to `star B`.

---

### Step 2: Applying `StarAlgHom.map_cfc`

Once `φ := lmul : A →⋆ₐ[ℂ] B(A)` is established as a star algebra hom:

```lean
-- Applying StarAlgHom.map_cfc with f = fun x => x ^ s
lemma lmul_rpow (A : Mₙℂ) (hA : 0 ≤ A) (s : ℝ≥0) :
    mulLeft ℂ (A ^ s) = (mulLeft ℂ A) ^ s := by
  -- lmul is a StarAlgHom, apply map_cfc
  have := StarAlgHom.map_cfc lmul (fun x => x ^ s) A
  simpa using this.symm
```

The hypotheses to discharge:
- `ha : IsSelfAdjoint A` (or `0 ≤ A` which implies it) — unlocks CFC
- `hφa : IsSelfAdjoint (mulLeft ℂ A)` — follows from `lmul` being a star hom
- `hf : ContinuousOn (· ^ s) (spectrum ℝ A)` — continuous on compact set ⊆ ℝ≥0
- `hφ : Continuous lmul` — follows from continuity of left multiplication

---

## Part III: Summary of Available Mathlib Infrastructure

### What exists

| Result | File | Status |
|--------|------|--------|
| `Algebra.lmul : A →ₐ[R] End R A` | `Algebra/Algebra/Bilinear.lean` | ✓ exists |
| `pow_mulLeft : mulLeft R a ^ n = mulLeft R (a ^ n)` | `Algebra/Algebra/Bilinear.lean` | ✓ exists |
| `pow_mulRight : mulRight R a ^ n = mulRight R (a ^ n)` | `Algebra/Algebra/Bilinear.lean` | ✓ exists |
| `NonUnitalAlgHom.Lmul : R →ₙₐ[𝕜] R →L[𝕜] R` | `Analysis/Normed/Operator/Mul.lean` | ✓ exists |
| `StarRing Rᵐᵒᵖ` instance | `Algebra/Star/Basic.lean` | ✓ exists |
| `starRingEquiv : R ≃+* Rᵐᵒᵖ` | `Algebra/Star/Basic.lean` | ✓ exists |
| `StarAlgHom.map_cfc` | `CStarAlgebra/CFC/Unique.lean` | ✓ exists |
| `A →⋆ₐ[ℂ] End ℂ A` for `lmul` | — | ✗ **missing** |
| `(mulLeft ℂ A)† = mulLeft ℂ (star A)` | — | ✗ **missing** |

### What needs to be proved (for this project)

1. **`lmul_isSelfAdjoint`**: `IsSelfAdjoint (mulLeft ℂ A) ↔ IsSelfAdjoint A`
   (follows from the trace adjoint calculation)

2. **`lmul_star`**: `mulLeft ℂ (star A) = star (mulLeft ℂ A)` (in `B(A)` with the
   Hilbert-Schmidt adjoint)
   → This is the key missing piece; prove it using `Matrix.trace_mul_comm` for matrices.

3. **`lmul_starAlgHom`**: Package the above into a `StarAlgHom A (B(A))`.

4. **`rpow_mulLeft`**: `mulLeft ℂ (A ^ s) = (mulLeft ℂ A) ^ s` for `s : ℝ≥0`
   → Follows from `StarAlgHom.map_cfc` applied to `lmul_starAlgHom`.

5. **`rpow_mulRight`**: Analogous result for right multiplication.

---

## Part IV: Recommended Lean Declaration Stubs

```lean
-- In LiebConcavity/ForMathlib.lean

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
-- NOTE: This requires equipping End(Matrix n n ℂ) with the Hilbert-Schmidt star structure.
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

---

## Key Files (relative to `.lake/packages/mathlib/Mathlib`)

| File | Content |
|------|---------|
| `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean` | `StarAlgHom.map_cfc`, `NonUnitalStarAlgHom.map_cfcₙ` |
| `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | `cfcHom`, its properties, composition |
| `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | Commutation with CFC |
| `Analysis/CStarAlgebra/Hom.lean` | Spectrum preservation, isometry for *-homomorphisms |
| `Algebra/Algebra/Bilinear.lean` | `Algebra.lmul`, `pow_mulLeft`, `pow_mulRight` |
| `Algebra/Module/LinearMap/Basic.lean` | `LinearMap.mulLeft`, `LinearMap.mulRight`, `mulLeft_mul`, `mulRight_mul` |
| `Analysis/Normed/Operator/Mul.lean` | `NonUnitalAlgHom.Lmul` (continuous version) |
| `Algebra/Star/Basic.lean` | `StarRing Rᵐᵒᵖ`, `starRingEquiv`, `starMulEquiv` |