# Abstract Approach: HilbertStarAlgebra (Avoiding the Two-Norm Problem)

## The Key Insight

**We do NOT need `CStarAlgebra H` on the abstract space `H`.**

The C\*-algebra properties we need live on the operator algebra `End(H) = H →L[ℂ] H`, not on `H` itself. Mathlib provides `CStarAlgebra (H →L[ℂ] H)` automatically when `H` is a complete inner product space.

For `H`, we only need:
- **Inner product space structure** — for `End(H)` to be a C\*-algebra
- **Ring + star structure** — for multiplication on H and left/right multiplication operators
- **Algebra ℂ** — coefficient ring
- **StarModule ℂ** — `star (c • x) = conj c • star x`
- **TopologicalRing** — so multiplication is continuous (needed for `L_a : H →L[ℂ] H`)
- **Compatibility**: `⟪a * x, y⟫ = ⟪x, star a * y⟫` — the single axiom

---

## Design Options for the Typeclass

### Option 1: `extends` (all-in-one)

```lean
class HilbertStarAlgebra (H : Type*) extends
    InnerProductSpace ℂ H, Ring H, StarRing H, Algebra ℂ H, StarModule ℂ H where
  [completeSpace : CompleteSpace H]
  [topRing : TopologicalRing H]
  inner_mul_left : ∀ (a x y : H), ⟪a * x, y⟫_ℂ = ⟪x, star a * y⟫_ℂ
```

**Pros:**
- Single typeclass to carry around
- Lean resolves parent instances automatically
- Cleaner function signatures: just `[HilbertStarAlgebra H]`

**Cons:**
- `extends InnerProductSpace ℂ H, Algebra ℂ H` creates a diamond on `Module ℂ H`
  - Both parents provide `Module ℂ H`
  - This is a **necessary diamond** (same underlying structure in all cases)
  - Lean 4's `extends` uses `old_uniq` to unify, but may cause slow typeclass search
- If the diamond causes issues, hard to debug

### Option 2: Mixin (separate assumptions)

```lean
class HilbertStarAlgebra (H : Type*)
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H]
    [TopologicalRing H] where
  inner_mul_left : ∀ (a x y : H), ⟪a * x, y⟫_ℂ = ⟪x, star a * y⟫_ℂ
```

**Pros:**
- No diamond: each parent is a separate `[]` parameter
- Module ℂ agreement enforced at call site
- Standard Lean 4 pattern (similar to how Mathlib does mixins)

**Cons:**
- Every declaration must carry all `[]` parameters explicitly
- More verbose: `variable [InnerProductSpace ℂ H] [CompleteSpace H] [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H] [TopologicalRing H] [HilbertStarAlgebra H]`
- Can mitigate with `variable` blocks at section level

**Decision**: Deferred to implementation. Try mixin first; fall back to `extends` if the verbosity is too painful.

---

## Why `TopologicalRing H` is Required

`StarAlgHomClass.map_cfc` (Unique.lean:483) has the hypothesis:
```
(hφ : Continuous φ := by fun_prop)
```
For our `lmulStarAlgHom : H →⋆ₐ[ℂ] (H →L[ℂ] H)`, we need this map to be continuous. The map `a ↦ L_a` is continuous iff left multiplication `(a, x) ↦ a * x` is jointly continuous, which is exactly `TopologicalRing H`.

On the scalar ring `R`, `map_cfc` also requires `[IsTopologicalSemiring R]`. For `R = ℝ` this is always satisfied.

For finite-dimensional `H` (like `HilbertMatrix n`), `TopologicalRing` is automatic since all bilinear maps on finite-dimensional spaces are continuous.

---

## Constructing `lmulStarAlgHom`

To build `H →⋆ₐ[ℂ] (H →L[ℂ] H)`, provide an `AlgHom` + star-preservation proof:

```lean
noncomputable def lmulStarAlgHom [HilbertStarAlgebra H] : H →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  ⟨Algebra.lmul ℂ H, fun a => star_lmul_eq a⟩
```

**Fields from `Algebra.lmul ℂ H : H →ₐ[ℂ] End ℂ H`** (Mathlib, `Algebra/Algebra/Bilinear.lean:137`):
- `map_zero'` ✓
- `map_add'` ✓
- `map_one'` ✓
- `map_mul'` ✓
- `commutes'` ✓

**New field — `map_star'`**: `L_{star a} = star(L_a)` in `End(H)`.

Proof:
```
⟪(L_a)†(x), y⟫ = ⟪x, L_a(y)⟫ = ⟪x, a*y⟫          (adjoint definition)
⟪L_{a†}(x), y⟫ = ⟪(star a)*x, y⟫ = ⟪x, a*y⟫         (inner_mul_left with star(star a) = a)
```
So `(L_a)† = L_{star a}`, i.e., `star(L_a) = L_{star a}`.

**No trace cyclicity needed** — only uses `inner_mul_left` and `star_star`.

---

## Critical Issue: CFC on H vs CFC on End(H)

**`H` is NOT a C\*-algebra**, so there is NO CFC on `H` itself.

This means `StarAlgHomClass.map_cfc` cannot be used in the direction `H → End(H)` because it requires `ContinuousFunctionalCalculus` on the **domain**. Our domain `H` doesn't have one.

**Impact on the proof**: The identity `L_{A^s} = L_A^s` (where `A^s` is computed on `H` or on `Matrix`) cannot be derived from `map_cfc` directly.

**Resolution options**:

1. **Concrete approach**: In `Lieb.lean`, compute `A^s` on `Matrix (Fin n) (Fin n) ℂ` (which IS a C\*-algebra via `open scoped Matrix.Norms.L2Operator`) and separately show `L_{A^s} = L_A^s` by density of polynomials (for which `pow_mulLeft` gives `L_A^n = L_{A^n}` for `n : ℕ`).

2. **Direct CFC argument**: Show that `cfc (· ^ s) (L_A) = L_{cfc (· ^ s) A}` by uniqueness of CFC, using the fact that `A ↦ L_A` is a continuous star-algebra hom and both sides are continuous star-algebra homs `C(σ(A)) → End(H)` agreeing on the identity function.

3. **Avoid the identity altogether**: State the abstract Lieb theorem purely in terms of `End(H)` operators, with no reference to elements of `H`. The trace identity (connecting to `Tr(A^s K* B^{1-s} K)`) becomes a separate concrete lemma.

**Option 3 is cleanest** for the abstract approach. The abstract theorem says "the inner product evaluation of GenPerspective is concave" — full stop. The concrete matrix translation happens in `Lieb.lean`.

---

## Abstract Lieb Theorem (No CFC on H)

```lean
/-- For any k : H, the functional (L, R) ↦ ⟪GenPerspective(·^s, id)(L, R)(k), k⟫
    is jointly concave on positive operators in End(H). -/
theorem LiebAbstract [HilbertStarAlgebra H] (k : H) (s : ℝ) (hs : 0 < s ∧ s < 1) :
    ConcaveOn ℝ {p : (H →L[ℂ] H) × (H →L[ℂ] H) | 0 ≤ p.1 ∧ 0 < p.2}
      (fun p => ⟪GenPerspective (H →L[ℂ] H) (· ^ s) id p k, k⟫_ℂ) := by
  -- 1. PowerMeanJointlyConcave gives operator concavity in End(H) (from Main.lean)
  -- 2. T ↦ ⟪T(k), k⟫ is a positive linear functional on End(H)
  -- 3. Concave composed with positive linear = concave
  sorry
```

**Key**: This theorem lives entirely in `End(H)`. No CFC on `H`, no matrices, no trace. Just inner product space + operator algebra.

---

## Concrete Instantiation (HilbertMatrix.lean + Lieb.lean)

### HilbertMatrix.lean

```lean
def HilbertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

-- Inner product via toMatrixNormedAddCommGroup 1 PosDef.one:
-- ⟪X, Y⟫ = Tr(Y * 1 * X†) = Tr(Y * X†) = Tr(X† * Y)

instance : HilbertStarAlgebra (HilbertMatrix n) := ⟨
  inner_mul_left := by  -- ⟪AX, Y⟫ = Tr((AX)†Y) = Tr(X†A†Y) = ⟪X, A†Y⟫
    sorry
⟩

lemma inner_eq_trace (X Y : HilbertMatrix n) :
    ⟪X, Y⟫_ℂ = Matrix.trace (star X * Y) := sorry
```

### Lieb.lean — The Bridge

The concrete Lieb theorem needs to show:
1. `A ≥ 0` (on Matrix) implies `L_A ≥ 0` (in End(HilbertMatrix))
2. `GenPerspective(·^s, id)(L_A, R_B)(K*) = A^s * K* * B^{1-s}` (trace identity)
3. `⟪A^s * K* * B^{1-s}, K*⟫ = Tr(A^s * K* * B^{1-s} * K)` (inner product = trace)

Step 2 is the hard part — it requires `L_A^s = L_{A^s}` and `R_B^s = R_{B^s}`, which bridge the two CFC computations (one on End(HilbertMatrix), one on Matrix).

---

## Advantages of the Abstract Approach

1. **No norm conflict**: H has one norm (from inner product). End(H) has its own C\*-norm.
2. **No CFC on H**: All CFC lives in End(H). Clean separation.
3. **Abstract Lieb theorem**: Works for any HilbertStarAlgebra, not just matrices.
4. **Matrix case is just an instance**: One `HilbertStarAlgebra (HilbertMatrix n)` declaration.
5. **CFC bridge is isolated**: The hard `L_{A^s} = L_A^s` identity is a concrete lemma, not an abstract requirement.
