# Plan: Specialize HStarAlgebra Theorems to n×n Complex Matrices

## Context

The project has abstract Lieb/Ando theorems in `Lieb.lean` for any `[HStarAlgebra ℂ H]` with
supporting instances. The final step is specializing to `H = Matrix (Fin n) (Fin n) ℂ` with
the Frobenius/trace inner product and Loewner (PSD) partial order.

### No type alias needed

Mathlib has **no global norm instances** on `Matrix n n ℂ`. All norm-carrying instances are
either `protected def` with `local instance`, or scoped (`Matrix.Norms.L2Operator`,
`Matrix.Norms.Frobenius`). So we can put our trace-inner-product norm directly on
`Matrix (Fin n) (Fin n) ℂ` without conflict, as long as we don't open those scopes.

---

## File

Create: `LeanLiebConcavity/Matrix.lean`
Update: `LeanLiebConcavity.lean` (add import)

---

## Step 1: (Removed — no type alias needed, work directly with `Matrix (Fin n) (Fin n) ℂ`)

---

## Step 2: NormedAddCommGroup + InnerProductSpace (trace inner product)

Use Mathlib's `toMatrixNormedAddCommGroup` and `toMatrixInnerProductSpace` with `M = 1`:

```lean
variable {n : ℕ}

noncomputable instance : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
  (1 : Matrix (Fin n) (Fin n) ℂ).toMatrixNormedAddCommGroup Matrix.PosDef.one

noncomputable instance : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  (1 : Matrix (Fin n) (Fin n) ℂ).toMatrixInnerProductSpace Matrix.PosDef.one.posSemidef
```

Inner product: `⟪x, y⟫ = (y * 1 * x†).trace = Tr(x† y)`

**Key files:**
- `Mathlib/Analysis/Matrix/Order.lean:362-394` — `toMatrixNormedAddCommGroup`, `toMatrixInnerProductSpace`
- `Mathlib/LinearAlgebra/Matrix/PosDef.lean:204` — `Matrix.PosDef.one`

---

## Step 3: NormedRing (Frobenius submultiplicativity)

Cannot use `frobeniusNormedRing` directly — it brings its own `NormedAddCommGroup` via `PiLp`,
creating a diamond with Step 2's inner-product-based norm.

**Approach**: Construct `NormedRing` manually using Step 2's `NormedAddCommGroup` + the ring
structure + `norm_mul_le` proof. For the latter, prove the norms are equal, then transfer
`frobenius_norm_mul`.

```lean
-- Prove: Frobenius norm = trace inner product norm
-- Both compute √(∑ᵢⱼ |aᵢⱼ|²), but through different paths
lemma frobenius_norm_eq_hilbert_norm (A : Matrix (Fin n) (Fin n) ℂ) :
    @norm _ frobeniusNormedAddCommGroup.toNorm A = ‖A‖ := sorry

noncomputable instance : NormedRing (Matrix (Fin n) (Fin n) ℂ) where
  __ := ‹Ring (Matrix (Fin n) (Fin n) ℂ)›
  __ := ‹NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)›
  norm_mul_le a b := by
    rw [← frobenius_norm_eq_hilbert_norm, ← frobenius_norm_eq_hilbert_norm,
        ← frobenius_norm_eq_hilbert_norm]
    exact frobenius_norm_mul a b
```

**Key files:**
- `Mathlib/Analysis/Matrix/Normed.lean:646` — `frobenius_norm_mul`
- `Mathlib/Analysis/Matrix/Normed.lean:511` — `frobeniusNormedAddCommGroup` (via PiLp)

---

## Step 4: CompleteSpace

```lean
instance : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstance
```

Finite-dimensional normed space → complete. Should be automatic via
`FiniteDimensional.complete`.

---

## Step 5: PartialOrder + StarOrderedRing + NonnegSpectrumClass (Loewner order)

These are scoped to `MatrixOrder` in Mathlib:

```lean
open scoped MatrixOrder

noncomputable instance : PartialOrder (Matrix (Fin n) (Fin n) ℂ) := Matrix.instPartialOrder
noncomputable instance : StarOrderedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instStarOrderedRing
noncomputable instance : NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instNonnegSpectrumClass
```

**Key file:** `Mathlib/Analysis/Matrix/Order.lean:77-105`

---

## Step 6: ContinuousFunctionalCalculus

```lean
instance : ContinuousFunctionalCalculus ℝ (Matrix (Fin n) (Fin n) ℂ) IsSelfAdjoint := inferInstance
```

From `Matrix.IsHermitian.instContinuousFunctionalCalculus` (independent of norm choice).

**Key file:** `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean:99`

---

## Step 7: PosSMulMono ℝ (Matrix (Fin n) (Fin n) ℂ)

No Mathlib instance exists. Prove manually:

```lean
instance : PosSMulMono ℝ (Matrix (Fin n) (Fin n) ℂ) where
  smul_le_smul_of_nonneg_left ha hb := by
    -- hb : B₁ ≤ B₂ means (B₂ - B₁).PosSemidef
    -- Need: a • B₁ ≤ a • B₂, i.e. (a • (B₂ - B₁)).PosSemidef
    -- Use: smul_sub, then show a • P is PSD when 0 ≤ a and P is PSD
    sorry
```

Core argument: `(a • P).PosSemidef` from `P.IsHermitian.smul` and `∀ v, 0 ≤ a * (v† ⬝ P v)`.

---

## Step 8: StarOrderedRing (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)

Automatic from Mathlib once `InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ)` + `CompleteSpace`:

```lean
instance : StarOrderedRing (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) := inferInstance
```

**Key file:** `Mathlib/Analysis/InnerProductSpace/StarOrder.lean:83`

---

## Step 9: HStarAlgebra Instance

The core construction. Must prove the two H*-algebra axioms:

```lean
instance : HStarAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) where
  inner_mul_left := by
    -- ⟪a * x, y⟫ = Tr(y * (a*x)†) = Tr(y * x† * a†)
    --            = Tr(a† * y * x†) (trace cyclicity)
    --            = ⟪x, a† * y⟫ = ⟪x, star a * y⟫
    sorry
  inner_mul_right := by
    -- ⟪x * a, y⟫ = Tr(y * (x*a)†) = Tr(y * a† * x†)
    --            = Tr((y * a†) * x†) = ⟪x, y * a†⟫ = ⟪x, y * star a⟫
    sorry
```

**Key Mathlib lemmas needed:**
- `Matrix.conjTranspose_mul : (A * B)ᴴ = Bᴴ * Aᴴ`
- `Matrix.trace_mul_cycle : Tr(A * B * C) = Tr(C * A * B)` (in `Mathlib/LinearAlgebra/Matrix/Trace.lean:161`)
- `star_eq_conjTranspose` for matrices
- An unfolding lemma: `inner_eq_trace : ⟪X, Y⟫_ℂ = (Y * X†).trace` (needs to be proved from the `toMatrixInnerProductSpace` definition with `M = 1`)

The `inner_eq_trace` helper is crucial — the inner product is defined through several layers
of abstraction (`PreInnerProductSpace.Core → InnerProductSpace.ofCore`). We may need
`set_option backward.isDefEq.respectTransparency false` to unfold it.

---

## Step 10: Specialized Theorem Statements

Once all instances compile, these are zero-proof:

```lean
theorem LiebConcavity_matrix (hs : 0 < s) (hs1 : s < 1) (x : Matrix (Fin n) (Fin n) ℂ) :
    ConcaveOn ℝ ... := LiebConcavity hs hs1 x

theorem LiebExtension_matrix (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) (x : Matrix (Fin n) (Fin n) ℂ) :
    ConcaveOn ℝ ... := LiebExtension hp hq hpq x

theorem AndoConvexity_matrix (hq : 1 ≤ q ∧ q ≤ 2) (hr : 0 < r) (hqr : q - r > 1)
    (x : Matrix (Fin n) (Fin n) ℂ) : ConvexOn ℝ ... := AndoConvexity hq hr hqr x
```

---

## Sorry Strategy

For initial development, `sorry`-stub these and fill in later:
- `frobenius_norm_eq_hilbert_norm` (Step 3)
- `PosSMulMono` proof (Step 7)
- `inner_mul_left` and `inner_mul_right` (Step 9)

The specialized theorems (Step 10) should need NO sorry — they just instantiate the abstract
theorems with `Matrix (Fin n) (Fin n) ℂ`.

---

## Verification

1. `lake build` should succeed (possibly with sorries in instance proofs)
2. The specialized theorems at Step 10 should compile with no sorry
3. Check that `#check @LiebConcavity (Matrix (Fin n) (Fin n) ℂ) _` resolves all instances

---

## Dependency Order

```
Step 2 (NormedAddCommGroup + InnerProductSpace)
  → Step 3 (NormedRing, depends on Step 2's norm)
  → Step 4 (CompleteSpace)
  → Step 5 (PartialOrder, StarOrderedRing — independent of norm)
  → Step 6 (CFC — independent of norm)
  → Step 7 (PosSMulMono — depends on Step 5's order)
  → Step 8 (StarOrderedRing on CLM — depends on Steps 2+4)
  → Step 9 (HStarAlgebra — depends on ALL above)
  → Step 10 (specialized theorems)
```
