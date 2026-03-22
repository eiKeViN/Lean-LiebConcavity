# Plan: Lieb Concavity Theorem via Operator Power Mean (v2 — Abstract Approach)

## Context

We want to prove Lieb's concavity theorem (Nik2013, Thm 1.2) following the paper's strategy:
1. Apply `PowerMeanJointlyConcave` (already proved at abstract C\*-algebra level) in the **operator algebra** `End(H)`
2. Show `L_A` (left mult) and `R_B` (right mult) are well-behaved elements of `End(H)`
3. Evaluate via the inner product: `⟨(R_B #_{(s,1)} L_A)(k), k⟩` is concave
4. For `H = HilbertMatrix n`, this gives `Tr(A^s K* B^{1-s} K)` concave

**Key insight (v2)**: We do NOT need `CStarAlgebra H` on the abstract space. The C\*-algebra structure lives on `End(H) = H →L[ℂ] H` (provided automatically by Mathlib when H is a complete inner product space). H itself only needs: ring, star, algebra, inner product, and compatibility.

## File Organization

```
LeanLiebConcavity/
├── ForMathlib.lean           — existing helper lemmas (UNCHANGED)
├── Defs.lean                 — GenPerspective, OperatorConvexOn/ConcaveOn (UNCHANGED)
├── Main.lean                 — PowerMeanJointlyConcave/Convex (UNCHANGED)
├── HilbertStarAlgebra.lean   — NEW: abstract class + lmulStarAlgHom + rmul + abstract Lieb
├── HilbertMatrix.lean        — NEW: HilbertMatrix type + HilbertStarAlgebra instance
└── Lieb.lean                 — NEW: concrete Lieb/Ando theorems for matrices
```

## Phase A: Abstract Class (HilbertStarAlgebra.lean)

### The HilbertStarAlgebra typeclass

Two design options (decision deferred):

#### Option 1: `extends` (single class, all-in-one)

```lean
class HilbertStarAlgebra (H : Type*) extends
    InnerProductSpace ℂ H, Ring H, StarRing H, Algebra ℂ H, StarModule ℂ H where
  [completeSpace : CompleteSpace H]
  inner_mul_left : ∀ (a x y : H), ⟪a * x, y⟫_ℂ = ⟪x, star a * y⟫_ℂ
  [topRing : TopologicalRing H]
```

**Pros**: Single import, one typeclass to carry around, Lean resolves all parent instances automatically.

**Cons**: `extends InnerProductSpace ℂ H, Algebra ℂ H` creates a diamond on `Module ℂ H`.
Both parents provide `Module ℂ H`. In this case it's a *necessary* diamond: the underlying
ℂ-module structure is genuinely the same (e.g. for matrices, `c • X` is always entrywise
scaling). Lean 4's `extends` mechanism should unify them via `old_uniq` synthesis, but this
can sometimes cause slow typeclass search or unexpected failures.

#### Option 2: Mixin (separate typeclass assumptions)

```lean
class HilbertStarAlgebra (H : Type*) [InnerProductSpace ℂ H] [CompleteSpace H]
    [Ring H] [StarRing H] [Algebra ℂ H] [StarModule ℂ H] [TopologicalRing H] where
  inner_mul_left : ∀ (a x y : H), ⟪a * x, y⟫_ℂ = ⟪x, star a * y⟫_ℂ
```

**Pros**: No diamond. Each parent typeclass is a separate `[]` parameter, so the caller
controls which instances are used. The `Module ℂ H` from `InnerProductSpace` and from
`Algebra ℂ H` must agree, but that's enforced at the call site, not inside the class.

**Cons**: Every declaration using `HilbertStarAlgebra` must also carry all the `[]`
parameters. More verbose signatures. May need `@[reducible]` abbreviation to bundle them.

### Why `TopologicalRing H` (or `IsTopologicalSemiring`)

`StarAlgHomClass.map_cfc` (Unique.lean:483) requires on the scalar ring `R`:
```
[CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
```
In our case `R = ℝ`, which satisfies all of these. But for the *domain* `A = H`, the CFC
instance `ContinuousFunctionalCalculus R A p` is on `End(H)`, not on `H` itself. The
topology requirement on `H` is needed so that:
1. `Algebra.lmul ℂ H : H →ₐ[ℂ] End ℂ H` produces **continuous** linear maps (i.e. `H →L[ℂ] H`)
2. The star-algebra hom `lmulStarAlgHom : H →⋆ₐ[ℂ] (H →L[ℂ] H)` is **continuous**
   (needed as explicit hypothesis `hφ : Continuous φ` in `map_cfc`)

For finite-dimensional `H`, `TopologicalRing` is automatic (all linear maps are continuous).
For the abstract class, we require it explicitly.

### Typeclass requirements summary

| On `H` | Purpose |
|---------|---------|
| `InnerProductSpace ℂ H` | Inner product, norm, topology |
| `CompleteSpace H` | So `H →L[ℂ] H` gets `CStarAlgebra` |
| `Ring H` | Multiplication on H |
| `StarRing H` | Star operation: `star (a * b) = star b * star a` |
| `Algebra ℂ H` | ℂ-algebra structure, `algebraMap ℂ H` |
| `StarModule ℂ H` | `star (c • x) = conj c • star x` |
| `TopologicalRing H` | Multiplication is continuous (or `IsTopologicalSemiring`) |
| `inner_mul_left` | `⟪a * x, y⟫ = ⟪x, star a * y⟫` — the compatibility axiom |

**Automatic consequences** (from Mathlib):
- `CStarAlgebra (H →L[ℂ] H)` — via `Analysis/CStarAlgebra/ContinuousLinearMap.lean`
- `StarOrderedRing (H →L[ℂ] H)` — via `Analysis/InnerProductSpace/StarOrder.lean`
- `PartialOrder (H →L[ℂ] H)` — from `StarOrderedRing`
- CFC for `IsSelfAdjoint` on `H →L[ℂ] H` — from `CStarAlgebra`
- `star T = T†` (adjoint) on `H →L[ℂ] H` — from inner product structure

## Phase B: Left Multiplication Star-Algebra Hom (HilbertStarAlgebra.lean)

### Constructing `lmulStarAlgHom`

To build `H →⋆ₐ[ℂ] (H →L[ℂ] H)`, we need all 7 fields of `StarAlgHom`:

| Field | Source |
|-------|--------|
| `toFun : H → (H →L[ℂ] H)` | `a ↦ L_a` (left multiplication) |
| `map_zero'` | `L_0 = 0` |
| `map_add'` | `L_{a+b} = L_a + L_b` |
| `map_one'` | `L_1 = id` |
| `map_mul'` | `L_{ab} = L_a ∘ L_b` |
| `commutes'` | `L_{c·1} = c · id` for `c : ℂ` |
| **`map_star'`** | **`L_{star a} = star(L_a) = (L_a)†`** |

Fields 1–6 come from `Algebra.lmul ℂ H : H →ₐ[ℂ] End ℂ H` (Mathlib, `Algebra/Algebra/Bilinear.lean:137`).

Field 7 is the new content. Proof sketch:
```
star(L_a) = (L_a)†   (star on H →L[ℂ] H is the adjoint)
⟪(L_a)†(x), y⟫ = ⟪x, L_a(y)⟫ = ⟪x, a*y⟫
⟪L_{star a}(x), y⟫ = ⟪(star a)*x, y⟫ = ⟪x, star(star a)*y⟫ = ⟪x, a*y⟫
So (L_a)† = L_{star a}, hence star(L_a) = L_{star a}.
```

Uses `inner_mul_left` (the compatibility axiom) and `star_star`. No trace cyclicity needed.

### Construction pattern

```lean
noncomputable def lmulStarAlgHom [HilbertStarAlgebra H] : H →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  ⟨Algebra.lmul ℂ H, fun a => by
    -- Prove: Algebra.lmul ℂ H (star a) = star (Algebra.lmul ℂ H a)
    -- i.e., L_{star a} = (L_a)†
    -- Use ContinuousLinearMap.ext_inner to reduce to inner product equality
    -- Then apply inner_mul_left
    sorry⟩
```

### CFC preservation: `L_{f(a)} = f(L_a)`

Immediate from `StarAlgHomClass.map_cfc` (Unique.lean:483):
```lean
theorem lmul_map_cfc [HilbertStarAlgebra H] (f : ℝ → ℝ) (a : H)
    (hf : ContinuousOn f (spectrum ℝ a)) :
    lmulStarAlgHom (cfc f a) = cfc f (lmulStarAlgHom a) :=
  StarAlgHomClass.map_cfc lmulStarAlgHom f a
```

**Requirements for `map_cfc` to fire:**
- `[AlgHomClass _ ℂ H (H →L[ℂ] H)]` ✓ (from StarAlgHom)
- `[StarHomClass _ H (H →L[ℂ] H)]` ✓ (from StarAlgHom)
- `Continuous lmulStarAlgHom` — need to prove; follows from `TopologicalRing H` (multiplication is continuous, so `a ↦ L_a` is continuous in the operator topology)
- `ContinuousFunctionalCalculus ℝ H p` — **WAIT**: This is CFC on `H`, not on `End(H)`. But `H` is NOT a C\*-algebra! We don't have CFC on `H`.

**CRITICAL ISSUE**: `StarAlgHomClass.map_cfc` requires CFC on BOTH the domain and codomain. We have CFC on `End(H)` (codomain), but NOT on `H` (domain) since `H` is not a C\*-algebra.

**Resolution**: We don't actually use `map_cfc` in the direction `H → End(H)`. Instead, we use the fact that `lmulStarAlgHom` is a star-algebra hom to show:
- `lmul(a) ≥ 0` when `a ≥ 0` (star-hom preserves positivity... but wait, positivity on `H` also needs `StarOrderedRing H` which we may not have)

**Revised approach**: The CFC preservation `L_{a^s} = L_a^s` is used in the **trace identity** (Phase D). But `a^s` is computed via CFC on `H`, which requires `CStarAlgebra H`. However, in the matrix case, `H = HilbertMatrix n` is NOT a C\*-algebra (wrong norm). So `a^s` must be computed on the original `Matrix` type and transferred.

This suggests the abstract Lieb theorem should NOT involve CFC on `H` at all. Instead:
- The abstract theorem works with `(L, R) : End(H) × End(H)` directly
- CFC is applied only in `End(H)` (which IS a C\*-algebra)
- The concrete matrix instantiation handles the translation `a ↦ L_a` and `a^s` separately

See revised Phase D/E below.

### Positivity preservation

If `a ≥ 0` in `H` (assuming some order on `H`), we need `L_a ≥ 0` in `End(H)`. For star-algebra homs, this follows from `StarOrderedRing` on both sides. But again, `H` may not have `StarOrderedRing`.

**Alternative**: We can prove `L_a ≥ 0` directly from the inner product:
```
L_a ≥ 0 in End(H)  ⟺  ⟪L_a(x), x⟫ ≥ 0 for all x
                    ⟺  ⟪a*x, x⟫ ≥ 0 for all x
```
This requires a notion of positivity on `H` that implies `⟪a*x, x⟫ ≥ 0`.

For matrices: `a ≥ 0` (positive semidefinite) implies `⟪AX, X⟫ = Tr(X†AX) ≥ 0` since `X†AX` is PSD and trace of PSD is nonneg. This is a concrete verification, not abstract.

## Phase C: Right Multiplication (HilbertStarAlgebra.lean)

`R_B(X) = X * B` is an anti-homomorphism. The conjugation trick is abstract:
```
R_B(X) = X * B = star(star(B) * star(X)) = star(L_{star B}(star X))
```

This identity holds in any `StarRing`. So `R_B = star_op ∘ L_{star B} ∘ star_op`.

For CFC preservation of `R_B`, we'd need the trace identity approach (Phase D).

**L and R commute** (abstract, trivial):
```
L_A(R_B(X)) = A * (X * B) = (A * X) * B = R_B(L_A(X))
```

## Phase D: Abstract Lieb's Theorem (HilbertStarAlgebra.lean)

**Revised approach**: The abstract theorem should work entirely at the `End(H)` level.

```lean
/-- Abstract Lieb concavity: for any k : H, the functional
    (L, R) ↦ ⟪GenPerspective(·^s, id)(L, R)(k), k⟫
    is jointly concave on positive operators in End(H). -/
theorem LiebAbstract [HilbertStarAlgebra H] (k : H) (s : ℝ) (hs : 0 < s ∧ s < 1) :
    ConcaveOn ℝ {p : (H →L[ℂ] H) × (H →L[ℂ] H) | 0 ≤ p.1 ∧ 0 < p.2}
      (fun p => ⟪GenPerspective (H →L[ℂ] H) (· ^ s) id p k, k⟫_ℂ) := by
  -- 1. PowerMeanJointlyConcave gives operator-level concavity in End(H)
  -- 2. T ↦ ⟪T(k), k⟫ is a positive linear functional
  -- 3. Composition of concave with linear = concave
  sorry
```

**No CFC on H needed.** The `GenPerspective` involves CFC on `End(H)`, which is a C\*-algebra.

## Phase E: Concrete Matrix Instantiation (HilbertMatrix.lean + Lieb.lean)

### HilbertMatrix.lean

```lean
def HilbertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

-- Inner product via toMatrixNormedAddCommGroup 1 PosDef.one
-- Ring, StarRing, Algebra ℂ, StarModule ℂ: transferred from Matrix
-- TopologicalRing: automatic (finite-dimensional)

instance : HilbertStarAlgebra (HilbertMatrix n) := ⟨
  inner_mul_left := by
    -- ⟪AX, Y⟫ = Tr((AX)†Y) = Tr(X†A†Y) = ⟪X, A†Y⟫
    sorry
⟩

-- Key lemma: inner product = trace
lemma inner_eq_trace (X Y : HilbertMatrix n) :
    ⟪X, Y⟫_ℂ = Matrix.trace (star X * Y) := sorry
```

### Lieb.lean

```lean
-- The bridge: connect abstract operators to matrix operations
-- For A : Matrix, the operator L_A in End(HilbertMatrix) applied to K*
-- gives A * K*, and ⟪A * K*, K*⟫ = Tr(K * A * K*) = Tr(A * K* * K)

theorem LiebConcavity (K : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs : 0 < s ∧ s < 1) :
    ConcaveOn ℝ
      {p : Matrix _ _ ℂ × Matrix _ _ ℂ | IsStrictlyPositive p.1 ∧ IsStrictlyPositive p.2}
      (fun p => Matrix.trace (p.1 ^ s * star K * p.2 ^ (1 - s) * K)) := by
  -- 1. Transfer A, B to HilbertMatrix n via hilbertMatrixEquiv
  -- 2. Show lmulStarAlgHom(A) = L_A and rmul(B) = R_B are positive in End(HilbertMatrix)
  -- 3. Apply LiebAbstract with k = star K (as HilbertMatrix)
  -- 4. Show GenPerspective(·^s, id)(L_A, R_B)(K*) = A^s * K* * B^{1-s}
  --    (this is the trace identity — requires L/R commute + CFC preservation)
  -- 5. Rewrite ⟪A^s * K* * B^{1-s}, K*⟫ = Tr(K * A^s * K* * B^{1-s}) = Tr(A^s * K* * B^{1-s} * K)
  sorry

-- Lieb extension, Ando convexity: similar pattern
```

## Dependency Graph (v2)

```
ForMathlib.lean (unchanged)
Defs.lean (unchanged, imports ForMathlib)
Main.lean (unchanged, imports Defs — PowerMeanJointlyConcave/Convex)

HilbertStarAlgebra.lean (imports Defs, Main):
  - HilbertStarAlgebra class definition
  - lmulStarAlgHom construction
  - rmul construction (via conjugation)
  - L/R commutativity
  - LiebAbstract theorem

HilbertMatrix.lean (imports HilbertStarAlgebra):
  - HilbertMatrix type alias
  - InnerProductSpace instance (via toMatrixNormedAddCommGroup 1 PosDef.one)
  - Ring/StarRing/Algebra ℂ/StarModule ℂ/TopologicalRing transfer
  - HilbertStarAlgebra instance
  - inner_eq_trace lemma

Lieb.lean (imports HilbertMatrix, Main):
  - Trace identity (connecting GenPerspective to matrix trace)
  - LiebConcavity theorem
  - LiebExtension theorem
  - AndoConvexity theorem
```

## Known Hard Sub-problems

1. **`extends` vs mixin for `HilbertStarAlgebra`** — Module ℂ diamond with `extends`; verbose signatures with mixin. See "Design Options" above. Decision deferred.

2. **Algebra structure transfer to `HilbertMatrix n`** — Ring, StarRing, Algebra ℂ, StarModule ℂ, TopologicalRing from `Matrix`. The type alias `def HilbertMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ` is definitionally equal but opaque to typeclass search. Need explicit instance declarations.

3. **CFC on H vs CFC on End(H)** — We do NOT have CFC on H (it's not a C\*-algebra). All CFC operations happen in End(H). The trace identity (Phase D/Lieb.lean) must bridge the gap: show that `cfc (· ^ s) (L_A) = L_{A^s}` where `A^s` is computed via a SEPARATE CFC on `Matrix` (which IS a C\*-algebra with the operator norm via `open scoped Matrix.Norms.L2Operator`).

4. **Commuting positive rpow in End(H)** — For the trace identity, need `(L_A · R_{B⁻¹})^s = L_A^s · R_{B^{-s}}` for commuting positive operators. This requires either joint CFC or a commutative subalgebra argument.

5. **Continuity of `lmulStarAlgHom`** — Needed for `StarAlgHomClass.map_cfc` if we use it. Follows from `TopologicalRing H` but need to formalize the proof.

6. **Inner product evaluation is positive linear** — `T ↦ ⟪T(k), k⟫` preserves concavity. Need to show this formally (linearity + positivity).

## Open Questions

1. **`extends` vs mixin** — deferred to implementation time. Document both, try mixin first.

2. **Do we need `StarOrderedRing H`?** — For positivity transfer `a ≥ 0 → L_a ≥ 0`. In the abstract theorem, we work with `(L, R) : End(H) × End(H)` directly, so we may not need an order on `H` at all. The concrete theorem translates `A ≥ 0` (on Matrix) to `L_A ≥ 0` (on End(HilbertMatrix)) directly.

3. **How does `A^s` (Matrix CFC) relate to `L_A^s` (End(H) CFC)?** — This is the key bridge. Both are rpow, but computed via different C\*-algebras. The identity `L_{A^s} = L_A^s` requires showing that `lmulStarAlgHom` intertwines the two CFC computations. But `StarAlgHomClass.map_cfc` requires CFC on H, which we don't have. Alternative: prove `L_{A^s} = L_A^s` directly using density of polynomials + continuity.

4. **Should `TopologicalRing H` be a field of `HilbertStarAlgebra` or a `[]` parameter?** — If using `extends`, it would be a field. If mixin, it's a `[]` parameter. The mixin approach is cleaner here since `TopologicalRing` is a standard Mathlib class.
