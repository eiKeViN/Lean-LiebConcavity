# Abstract Approach: HStarAlgebra (Avoiding the Two-Norm Problem)

## Mathematical Background: H\*-algebras

The structure we need has an established name in mathematics: **H\*-algebra** (Ambrose 1945).

**Definition** (W. Ambrose, "Structure theorems for a special class of Banach algebras,"
*Trans. AMS* 57 (1945), 364–386). An **H\*-algebra** is a Banach \*-algebra whose norm
arises from a scalar-valued inner product satisfying:

    ⟨a · x, y⟩ = ⟨x, a* · y⟩

**Classification theorem** (Ambrose 1945): Every H\*-algebra decomposes as an orthogonal
direct sum of simple H\*-algebras, and each simple H\*-algebra is isomorphic to the
algebra of **Hilbert–Schmidt operators** on some Hilbert space (with the Hilbert–Schmidt /
Frobenius inner product). For finite dimensions, every simple H\*-algebra is
`Matrix (Fin n) (Fin n) ℂ` with trace inner product.

**Related but distinct concepts:**

| Name | Inner product values | Extra axioms | In Mathlib? |
|------|---------------------|--------------|-------------|
| **H\*-algebra** (Ambrose 1945) | Scalars (ℂ) | — | **No** |
| **Hilbert algebra** (Dixmier/Tomita-Takesaki) | Scalars (ℂ) | ⟨x,y⟩ = ⟨y\*, x\*⟩ + bounded L_x + density | **No** |
| **Hilbert C\*-module** (`CStarModule A E`) | Algebra A | ⟨x, a•y⟩\_A = a · ⟨x,y⟩\_A | **Yes** |
| **C\*-algebra as module over itself** | Self (A) | ⟨x, y⟩\_A = x\* · y | **Yes** (instance) |

The crucial distinction from `CStarModule`: CStarModule has an **A-valued** inner product
and uses an external module action `•`, while an H\*-algebra has a **ℂ-valued** inner product
and uses its own **ring multiplication**. These are genuinely different structures.

## The Key Insight

**We do NOT need `CStarAlgebra H` on the abstract space `H`.**

The C\*-algebra properties we need live on the operator algebra `End(H) = H →L[ℂ] H`, not on `H` itself. Mathlib provides `CStarAlgebra (H →L[ℂ] H)` automatically when `H` is a complete inner product space.

For `H`, we only need:
- **Inner product space structure** — for `End(H)` to be a C\*-algebra
- **Ring + star structure** — for multiplication on H and left/right multiplication operators
- **Algebra ℂ** — coefficient ring
- **StarModule ℂ** — `star (c • x) = conj c • star x`
- **TopologicalRing** — so multiplication is continuous (needed for `L_a : H →L[ℂ] H`)
- **Compatibility**: `⟪a * x, y⟫ = ⟪x, star a * y⟫` — the single axiom (the H\*-algebra axiom)

---

## Design Options for the Typeclass

### Option 1: `extends` (all-in-one)

```lean
class HStarAlgebra (H : Type*) extends
    InnerProductSpace ℂ H, Ring H, StarRing H, Algebra ℂ H, StarModule ℂ H where
  [completeSpace : CompleteSpace H]
  [topRing : TopologicalRing H]
  inner_mul_left : ∀ (a x y : H), ⟪a * x, y⟫_ℂ = ⟪x, star a * y⟫_ℂ
```

**Pros:**
- Single typeclass to carry around
- Lean resolves parent instances automatically
- Cleaner function signatures: just `[HStarAlgebra H]`

**Cons:**
- `extends InnerProductSpace ℂ H, Algebra ℂ H` creates a diamond on `Module ℂ H`
  - Both parents provide `Module ℂ H`
  - This is a **necessary diamond** (same underlying structure in all cases)
  - Lean 4's `extends` uses `old_uniq` to unify, but may cause slow typeclass search
- If the diamond causes issues, hard to debug

### Option 2: Mixin (separate assumptions)

```lean
class HStarAlgebra (H : Type*)
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
- More verbose: `variable [InnerProductSpace ℂ H] [CompleteSpace H] [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H] [TopologicalRing H] [HStarAlgebra H]`
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
noncomputable def lmulStarAlgHom [HStarAlgebra H] : H →⋆ₐ[ℂ] (H →L[ℂ] H) :=
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

## CFC on H: Transfer from End(H) via ClosedRange

### Background

**`H` is NOT a C\*-algebra**, but the `ContinuousFunctionalCalculus` class does NOT
require `CStarAlgebra`. It only requires:

```
[Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]
```

All of which an `HStarAlgebra` has. So the question is purely whether we can
**construct** a CFC instance on H, not whether H has enough structure to state one.

### Strategy: pullback via `ι = lmulStarAlgHom : H →⋆ₐ[ℂ] End(H)`

End(H) is a C\*-algebra with CFC. We transfer it to H via ι.

### Spectrum equality: `σ_R(a) = σ_R(L_a)`

**Direction `σ(L_a) ⊆ σ(a)`**: Free from `AlgHom.spectrum_apply_subset`.

**Direction `σ(a) ⊆ σ(L_a)`**: If `L_{a-λ}` is invertible in End(H) (i.e., `x ↦ (a-λ)x`
is bijective), we need `a - λ` invertible in H.

- **Right inverse**: `L_{a-λ}` surjective → `∃ b, (a-λ)·b = 1`. ✓
- **Left inverse**: Use the H\*-algebra star. `R_{a-λ}(x) = x(a-λ) = star(L_{star(a-λ)}(star(x)))`.
  So `R_{a-λ}` is bijective iff `L_{star(a-λ)}` is bijective.
  - For **self-adjoint** `a` with real `λ`: `star(a-λ) = a - λ`, so `L_{star(a-λ)} = L_{a-λ}`,
    which is bijective by assumption. ✓
  - For **normal** `a` with complex `λ`: `σ(L_{star(a)}) = conj(σ(L_a))` (C\*-algebra theory
    on End(H)), so `λ ∉ σ(L_a) ⟹ conj(λ) ∉ σ(L_{star(a)})`, and `star(a-λ) = star(a) - conj(λ)`. ✓

**Result**: `σ_R(a) = σ_R(L_a)` for self-adjoint and normal elements.

### CFC axioms checklist

| CFC axiom | How to satisfy |
|-----------|---------------|
| `predicate_zero` | `IsSelfAdjoint 0` — trivial |
| `compactSpace_spectrum a` | `σ(a) = σ(L_a)`, and `σ(L_a)` is compact (C\*-algebra on End(H)) |
| `spectrum_nonempty a ha` | `σ(a) = σ(L_a)`, and `σ(L_a)` is nonempty (C\*-algebra + Nontrivial) |
| `exists_cfc_of_predicate a ha` | Need `φ_H : C(σ(a), R) →⋆ₐ[R] H` — see below |

### The key construction: `φ_H(f) = ι⁻¹(cfc f (L_a))`

Define `φ_H(f) = ι⁻¹(cfcHom(L_a)(f))`. This requires:

**`cfc f (L_a) ∈ range(ι)`** for all continuous f.

- `L_a ∈ range(ι)` — by definition.
- `range(ι)` is a star-subalgebra of End(H) — since ι is a star-alg hom.
- `cfc f (L_a)` is in the closure of the star-subalgebra generated by `L_a` — by CFC construction.
- So `cfc f (L_a) ∈ closure(range(ι))`.

We need `closure(range(ι)) = range(ι)`, i.e., **`range(ι)` is closed in End(H)**.

### The `ClosedRange` hypothesis

We add this as an explicit hypothesis:

```lean
variable [HStarAlgebra H] [TopologicalRing H]
    (hι : Function.ClosedRange (lmulStarAlgHom (H := H)))
```

- For **finite-dimensional** H: automatic (all subspaces are closed).
- For **infinite-dimensional** H: a genuine requirement. Holds for all H\*-algebras arising
  as Hilbert–Schmidt operator algebras (Ambrose classification), but must be verified per instance.

### Full CFC transfer theorem

```lean
/-- An HStarAlgebra with closed lmul range admits a CFC transferred from End(H). -/
instance [HStarAlgebra H] [TopologicalRing H]
    (hι : Function.ClosedRange (lmulStarAlgHom (H := H))) :
    ContinuousFunctionalCalculus ℝ H IsSelfAdjoint where
  predicate_zero := .zero
  compactSpace_spectrum a := by -- transfer from σ(L_a)
    sorry
  spectrum_nonempty a ha := by -- transfer from σ(L_a)
    sorry
  exists_cfc_of_predicate a ha := by
    -- φ_H := ι⁻¹ ∘ cfcHom(L_a) : C(σ(a), ℝ) →⋆ₐ[ℝ] H
    -- Well-defined because cfcHom(L_a)(f) ∈ range(ι) (closed star-subalgebra containing L_a)
    -- Continuous: cfcHom is continuous, ι⁻¹ on range(ι) is continuous (open mapping thm)
    -- Injective: cfcHom injective + ι injective
    -- Maps id to a: cfcHom maps id to L_a, ι⁻¹(L_a) = a
    sorry
```

### Payoff: `map_cfc` fires

With CFC on H, `StarAlgHomClass.map_cfc` gives us the bridge identity for free:

```lean
theorem lmul_map_cfc [HStarAlgebra H] [TopologicalRing H]
    (hι : Function.ClosedRange (lmulStarAlgHom (H := H)))
    (f : ℝ → ℝ) (a : H) (hf : ContinuousOn f (spectrum ℝ a)) :
    lmulStarAlgHom (cfc f a) = cfc f (lmulStarAlgHom a) :=
  StarAlgHomClass.map_cfc lmulStarAlgHom f a
```

In particular: `L_{a^s} = L_a^s`. **No density-of-polynomials argument needed.**

### UniqueHom on H

`StarAlgHomClass.map_cfc` requires `[ContinuousMap.UniqueHom R B]` on the **codomain** only.
For our use case (φ = lmulStarAlgHom, codomain = End(H)), UniqueHom on End(H) is already provided.

If we ever need map_cfc with H as codomain, UniqueHom on H follows from:
- `ι` is injective and continuous
- UniqueHom on End(H)
- Two star-alg homs `C(s, R) → H` that agree on id must agree everywhere, because after
  composing with ι they become two star-alg homs `C(s, R) → End(H)` agreeing on id, hence
  equal by UniqueHom on End(H), hence equal before composing (ι injective).

---

## Abstract Lieb Theorem

```lean
/-- For any k : H, the functional (L, R) ↦ ⟪GenPerspective(·^s, id)(L, R)(k), k⟫
    is jointly concave on positive operators in End(H). -/
theorem LiebAbstract [HStarAlgebra H] (k : H) (s : ℝ) (hs : 0 < s ∧ s < 1) :
    ConcaveOn ℝ {p : (H →L[ℂ] H) × (H →L[ℂ] H) | 0 ≤ p.1 ∧ 0 < p.2}
      (fun p => ⟪GenPerspective (H →L[ℂ] H) (· ^ s) id p k, k⟫_ℂ) := by
  -- 1. PowerMeanJointlyConcave gives operator concavity in End(H) (from Main.lean)
  -- 2. T ↦ ⟪T(k), k⟫ is a positive linear functional on End(H)
  -- 3. Concave composed with positive linear = concave
  sorry
```

**Key**: This theorem lives entirely in `End(H)`. No CFC on `H`, no matrices, no trace.

The abstract theorem does NOT require `ClosedRange`. CFC on H is only needed for the
**bridge** `L_{a^s} = L_a^s` used in the concrete instantiation.

---

## Concrete Instantiation (HilbertMatrix.lean + Lieb.lean)

### HilbertMatrix.lean

```lean
def HilbertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

-- Inner product via toMatrixNormedAddCommGroup 1 PosDef.one:
-- ⟪X, Y⟫ = Tr(Y * 1 * X†) = Tr(Y * X†) = Tr(X† * Y)

instance : HStarAlgebra (HilbertMatrix n) := ⟨
  inner_mul_left := by  -- ⟪AX, Y⟫ = Tr((AX)†Y) = Tr(X†A†Y) = ⟪X, A†Y⟫
    sorry
⟩

-- ClosedRange is automatic (finite-dimensional)
instance : Function.ClosedRange (lmulStarAlgHom (H := HilbertMatrix n)) := by
  exact LinearMap.closedRange_of_finiteDimensional _  -- or similar

-- CFC instance is now automatic from the transfer theorem above

lemma inner_eq_trace (X Y : HilbertMatrix n) :
    ⟪X, Y⟫_ℂ = Matrix.trace (star X * Y) := sorry
```

### Lieb.lean — The Bridge

The concrete Lieb theorem needs to show:
1. `A ≥ 0` (on Matrix) implies `L_A ≥ 0` (in End(HilbertMatrix))
2. `L_{A^s} = L_A^s` — **now free from `lmul_map_cfc`** (via CFC transfer + map_cfc)
3. `GenPerspective(·^s, id)(L_A, R_B)(K*) = A^s * K* * B^{1-s}` (trace identity, uses step 2)
4. `⟪A^s * K* * B^{1-s}, K*⟫ = Tr(A^s * K* * B^{1-s} * K)` (inner product = trace)

---

## Advantages of the Abstract Approach

1. **No norm conflict**: H has one norm (from inner product). End(H) has its own C\*-norm.
2. **CFC on H without C\*-algebra**: Transferred from End(H) via `ClosedRange lmulStarAlgHom`.
3. **`L_{a^s} = L_a^s` for free**: Direct from `StarAlgHomClass.map_cfc`, no ad hoc argument.
4. **Abstract Lieb theorem**: Works for any HStarAlgebra, not just matrices.
5. **Matrix case is just an instance**: `HStarAlgebra (HilbertMatrix n)` + `ClosedRange` (automatic).
6. **Infinite-dimensional support**: Works for any H\*-algebra with closed lmul range.
