# Plan: `lmulStarAlgHom` and `Lmul (cfc f a) = cfc f (Lmul a)`

## Context

We want to prove that left multiplication commutes with CFC: `L_{f(a)} = f(L_a)`.
The Mathlib lemma `StarAlgHom.map_cfc` gives this once `Lmul` is packaged as a
`StarAlgHom`. This plan restructures the file to define the `AlgHom` / `StarAlgHom`
as the **primary objects**, with `Lmul` derived from them.

---

## Tutorial: Mathlib's Homomorphism Class Hierarchy

### The Bundled/Unbundled Pattern

Mathlib uses a two-layer pattern for algebraic morphisms:

1. **Bundled structure** (`AlgHom`, `StarAlgHom`): a concrete type carrying the
   function AND all its proofs. Written `A →ₐ[R] B` or `A →⋆ₐ[R] B`.

2. **Unbundled class** (`AlgHomClass`, `StarHomClass`): a typeclass saying "any
   type `F` with `FunLike F A B` that also satisfies these properties". Lets
   polymorphic lemmas work on *any* function-like type.

### Extends chains

```
StarAlgHom R A B
  extends AlgHom R A B       -- adds: map_star'
    extends RingHom A B       -- adds: commutes' (with algebraMap)
```

`StarAlgHom` carries 7 fields: `toFun`, `map_zero'`, `map_add'`, `map_one'`,
`map_mul'`, `commutes'`, `map_star'`.

### Why there is no `StarAlgHomClass`

A star algebra hom is characterized by the *conjunction* of two existing classes:
- `AlgHomClass F R A B` (algebra hom properties)
- `StarHomClass F A B` (preserves star)

This is what `StarAlgHom.map_cfc` requires in its variable block.

### Key construction patterns from `Algebra.Hom`

- **`AlgHom.ofLinearMap f map_one map_mul`** (line 316): Promote a `LinearMap`
  to `AlgHom` — `commutes'` comes free from linearity + `map_one`:
  ```lean
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one, f.map_smul, map_one]
  ```

- **`AlgHom.mk' f h`** (line 221): Make `AlgHom` from `RingHom` + smul-compat.

- **Coercion infrastructure**: Lots of `@[simp]` `coe_*` lemmas to manage
  the diamond between different views of the same map.

---

## What `StarAlgHom.map_cfc` Requires

```lean
lemma StarAlgHom.map_cfc (φ : A →⋆ₐ[S] B) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a))
    (hφ : Continuous φ)
    (ha : p a) (hφa : q (φ a)) :
    φ (cfc f a) = cfc f (φ a)
```

Instantiation for our case: `R = ℝ`, `S = 𝕜`, `A = H`, `B = H →L[𝕜] H`,
`p = q = IsSelfAdjoint`, `φ = lmulStarAlgHom`.

---

## Step 0: Typeclass Audit — **COMPLETED**

Audit was run with `[NormedAddCommGroup H] [HStarAlgebra 𝕜 H] [Algebra 𝕜 H]
[IsTopologicalSemiring H] [CompleteSpace H]`.

### Results

| Instance | Status | Source |
|----------|--------|--------|
| `Semiring H` | ✅ | HStarAlgebra |
| `StarRing H` | ✅ | HStarAlgebra |
| `TopologicalSpace H` | ✅ | NormedAddCommGroup |
| `Algebra 𝕜 H` | ✅ | variable |
| `Star H` | ✅ | StarRing |
| `InnerProductSpace 𝕜 H` | ✅ | HStarAlgebra |
| `NormedAddCommGroup H` | ✅ | parameter |
| `NormedSpace 𝕜 H` | ✅ | InnerProductSpace |
| `Semiring (H →L[𝕜] H)` | ✅ | NormedRing (Mathlib) |
| `NormedAddCommGroup (H →L[𝕜] H)` | ✅ | Mathlib |
| `NormedAlgebra 𝕜 (H →L[𝕜] H)` | ✅ | Mathlib |
| `Algebra 𝕜 (H →L[𝕜] H)` | ✅ | NormedAlgebra |
| `Star (H →L[𝕜] H)` | ✅ | adjoint (needs CompleteSpace) |
| `StarRing (H →L[𝕜] H)` | ✅ | adjoint |
| `Algebra ℝ H` | ❌ | needs `[IsScalarTower ℝ 𝕜 H]` variable |
| `IsScalarTower ℝ 𝕜 H` | ❌ | needs explicit variable |
| `IsScalarTower ℝ 𝕜 (H →L[𝕜] H)` | ❌ | needs explicit variable |

### Key findings

1. **`SeminormedAddCommGroup` must be upgraded to `NormedAddCommGroup`** in the
   class parameter. With `SeminormedAddCommGroup`, Lean cannot resolve
   `NormedAddCommGroup H` because the resolution path goes through `𝕜`
   (`HStarAlgebra 𝕜 H → InnerProductSpace 𝕜 H → NormedAddCommGroup H`) and
   Lean cannot infer `𝕜` from a goal that doesn't mention it. With
   `NormedAddCommGroup H` as a direct parameter, the issue vanishes.
   **This change is required** — it was made to the class.

2. **Module diamond exposed**: After fixing the parameter, the `Lmul` definition
   broke with:
   ```
   Type mismatch: (Algebra.lmul 𝕜 H) a has type Module.End 𝕜 H
   but is expected to have type H →ₗ[𝕜] H
   ```
   `Module.End 𝕜 H` IS `H →ₗ[𝕜] H` by definition, but with two `Module 𝕜 H`
   instances in scope (`Algebra.toModule` from `[Algebra 𝕜 H]` variable and
   `NormedSpace.toModule` from `InnerProductSpace`), the elaborator picks different
   ones for `Algebra.lmul` vs the CLM constructor, causing the mismatch.

3. **ℝ scalar tower not free**: `Algebra ℝ H`, `IsScalarTower ℝ 𝕜 H` don't
   synthesize automatically — must be added as explicit variables in the CFC section.

---

## Step 1: Build `lmulAlgHom : H →ₐ[𝕜] (H →L[𝕜] H)`

No `CompleteSpace` needed. This is the primary algebraic object.

```lean
-- No [Algebra 𝕜 H] needed separately — comes from [HStarAlgebra 𝕜 H] via extends.
variable [IsTopologicalSemiring H]

noncomputable def lmulAlgHom : H →ₐ[𝕜] (H →L[𝕜] H) where
  toFun a :=
    { toFun    := (a * ·)
      map_add' := mul_add a
      map_smul' := fun c x => mul_smul_comm c a x   -- SMulCommClass 𝕜 H H from Algebra
      cont     := continuous_const_mul a }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' := fun a b => by ext; simp [add_mul]     -- plain simp misses add_mul here
  commutes' := fun c => by ext; simp [Algebra.algebraMap_eq_smul_one]
```

**Design note**: We wrap `Algebra.lmul 𝕜 H a` (a `LinearMap`) with
`continuous_const_mul a` (from `IsTopologicalSemiring`) to produce a CLM.
The algebraic fields follow from `Algebra.lmul`'s properties via `simp`.

### Derived definitions and API

```lean
/-- Left multiplication by `a`, as a continuous linear map. -/
abbrev Lmul (a : H) : H →L[𝕜] H := lmulAlgHom 𝕜 a

@[simp] theorem Lmul_apply {a x : H} : Lmul 𝕜 a x = a * x := rfl

-- These now follow from AlgHom/RingHom properties:
@[simp] theorem Lmul_one : Lmul 𝕜 1 = (1 : H →L[𝕜] H) := map_one (lmulAlgHom 𝕜)
@[simp] theorem Lmul_zero : Lmul 𝕜 0 = (0 : H →L[𝕜] H) := map_zero (lmulAlgHom 𝕜)
@[simp] theorem Lmul_mul {a b : H} : Lmul 𝕜 a * Lmul 𝕜 b = Lmul 𝕜 (a * b) :=
  (map_mul (lmulAlgHom 𝕜) a b).symm
@[simp] theorem Lmul_add {a b : H} : Lmul 𝕜 a + Lmul 𝕜 b = Lmul 𝕜 (a + b) :=
  (map_add (lmulAlgHom 𝕜) a b).symm
```

**Advantage**: Most `Lmul_*` lemmas become one-liners delegating to `map_*`.

end AlgHom
```

---

## Step 2: Upgrade to `lmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H)`

Requires `[CompleteSpace H]` so that `star` on `H →L[𝕜] H` is `adjoint`.

```lean
section StarAlgHom
variable [Algebra 𝕜 H] [IsTopologicalSemiring H] [CompleteSpace H]

theorem Lmul_star (a : H) :
    Lmul 𝕜 (star a) = star (Lmul 𝕜 a) := by
  rw [star_eq_adjoint]
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    fun x y => by simp [inner_left_mul_eq]

noncomputable def lmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H) :=
  { lmulAlgHom 𝕜 with
    map_star' := Lmul_star 𝕜 }
```

**Key proof**: `eq_adjoint_iff` (Adjoint.lean:160) says
`A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫`. Our H*-algebra axiom `inner_left_mul_eq`
gives exactly `⟪(star a) * x, y⟫ = ⟪x, a * y⟫` (after unfolding star-star).

```
end StarAlgHom
```

---

## Step 3: Apply `map_cfc`

```lean
section CFC
variable [Algebra 𝕜 H] [IsTopologicalSemiring H] [CompleteSpace H]
variable [ContinuousFunctionalCalculus ℝ H IsSelfAdjoint]  -- assumed
variable [IsScalarTower ℝ 𝕜 H] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

theorem Lmul_map_cfc (f : ℝ → ℝ) (a : H)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (hφ : Continuous (lmulStarAlgHom 𝕜 : H → H →L[𝕜] H) := by fun_prop)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    lmulStarAlgHom 𝕜 (cfc f a) = cfc f (lmulStarAlgHom 𝕜 a) :=
  StarAlgHom.map_cfc (lmulStarAlgHom 𝕜) f a

end CFC
```

**Notes on `hφ`**: Continuity of `lmulStarAlgHom` as `H → H →L[𝕜] H` may not
discharge by `fun_prop`. If not, either:
- Add it as an explicit hypothesis
- Add `NormedRing H` (gives `‖Lmul a‖ ≤ ‖a‖`)
- Sorry it for now (provable for finite-dimensional cases)

---

## Step 4: Rmul (keep as standalone)

`Rmul` is an **anti**-homomorphism (`R_{ab} = R_b ∘ R_a`), so it cannot be a
`StarAlgHom`. Keep the existing standalone definition and API unchanged.

---

## Obstacles

### A. Diamond: `Add H` / `SMul 𝕜 H` / `Module 𝕜 H` — **RESOLVED**

**Root cause** (deeper than originally diagnosed): The outer `[NormedAddCommGroup H]`
parameter introduced a **separate** `Add H` / `SMul 𝕜 H` instance alongside those from
`Semiring H` and `InnerProductSpace 𝕜 H` (via extends). Lean 4's `extends` only unifies
fields within the `extends` chain; it does NOT unify an outer instance parameter with an
in-chain instance. So even with `Algebra 𝕜 H` in extends (the original "Option A"),
`mul_add a` (which used `Semiring.toAdd`) did not match the `map_add'` field expected type
(which used `NormedAddCommGroup.toAdd`).

**Option A** (tried): Add `Algebra 𝕜 H` to `extends`. This fixed the `Module` diamond
but NOT the `Add`/`SMul` diamonds because `[NormedAddCommGroup H]` was still external.

**Option B** (tried with Option A): Build the `LinearMap` inline without `Algebra.lmul`.
Still failed — same `Add`/`SMul` mismatch because the outer parameter was still there.

**Actual fix**: Move `NormedAddCommGroup H` from the outer parameter INTO the `extends`
chain. Then all `Add H`, `SMul 𝕜 H`, `Module 𝕜 H` instances are unified by `extends`.

```lean
-- BEFORE:
class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] extends
    Semiring H, Algebra 𝕜 H, InnerProductSpace 𝕜 H, StarRing H where

-- AFTER (current):
class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] extends
    NormedAddCommGroup H, Semiring H, Algebra 𝕜 H, InnerProductSpace 𝕜 H, StarRing H where
```

Consequence: all variable blocks drop `[NormedAddCommGroup H]` (it comes from
`[HStarAlgebra 𝕜 H]` automatically).

**Correct `map_smul'`**: `mul_smul_comm c a x` directly (no `.symm`) gives
`a * (c • x) = c • (a * x)` which matches the `map_smul'` expected type.

**Correct outer `map_add'`**: `by ext; simp [add_mul]` (plain `simp` can't find `add_mul`
on its own here).

### B. Continuity of `lmulStarAlgHom`

Not automatic from `IsTopologicalSemiring`. Options:
- `NormedRing H` (submultiplicative norm → `‖Lmul a‖ ≤ ‖a‖`)
- `FiniteDimensional 𝕜 H` (all linear maps continuous)
- Explicit hypothesis on `Lmul_map_cfc`
- Sorry for now

### C. CFC on `H`

Assumed as `[ContinuousFunctionalCalculus ℝ H IsSelfAdjoint]`. Future construction
would transfer CFC from `H →L[𝕜] H` via `lmulStarAlgHom` (requires proving
spectrum equality and closed range).

### D. `Ring` vs `Semiring`

Keep `Semiring` in the class. Add `[Ring H]` as variable in the `CFC` section
(needed for `spectrum` which requires subtraction).

---

## Summary of changes to `HStarAlgebra.lean`

0. **Already done (Step 0)**:
   - Changed `[SeminormedAddCommGroup H]` → `[NormedAddCommGroup H]` in class
   - Removed `set_option trace.Meta.synthInstance true`
   - Added `end StarAlgHom` to close the dangling section

**Step 1 progress** (partially done):

- ✅ Class restructured: `[NormedAddCommGroup H]` moved from outer param into `extends` chain
- ✅ Variable block updated: `[NormedAddCommGroup H]` dropped from namespace variable
- ✅ `lmulAlgHom` defined with inline `LinearMap` (Option B): `toFun := (a * ·)`,
  `map_add' := mul_add a`, `map_smul' := mul_smul_comm c a x`, `cont := continuous_const_mul a`
- ✅ `Lmul` is now `abbrev Lmul (a : H) := lmulAlgHom 𝕜 a`
- ✅ `Lmul_zero/one/add/mul` simplified to `map_*` one-liners
- ⬜ `section StarAlgHom` cleanup: still has `[NormedAddCommGroup H]`, broken instances
  (`aa`, `a`, `aaaaa`), broken `Lmul_commutes`, `variable [AlgHomClass ...]`, stale stub comment
- ⬜ TypeclassAudit section still present (to delete)

1. **Delete** remaining broken code: the `instance aa`, `instance a`, `instance aaaaa`,
   and dangling `variable [AlgHomClass ...]` lines (current lines ~209–223)

2. **Add import**: `import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique`

3. **Restructure** the file into sections:
   - `section InnerProduct` — the H*-algebra axiom lemmas (unchanged)
   - `section AlgHom` — `lmulAlgHom`, derived `Lmul`/`Rmul` API
   - `section StarAlgHom` — `Lmul_star`, `lmulStarAlgHom` (adds `CompleteSpace`)
   - `section CFC` — `Lmul_map_cfc` (adds CFC hypothesis)

4. **Existing `Lmul`** becomes `abbrev Lmul a := lmulAlgHom 𝕜 a`. Existing
   `Lmul_*` lemmas become one-liners via `map_*`.

5. **Existing `Rmul`** stays as-is (anti-homomorphism, no AlgHom packaging).

6. **Existing symmetry/positivity section** stays after Rmul (uses `Lmul` abbrev).

---

## File to modify

- [HStarAlgebra.lean](../LeanLiebConcavity/HStarAlgebra.lean)

## Verification

1. `lake build LeanLiebConcavity.HStarAlgebra` passes
2. `#check @Lmul_map_cfc` shows correct type
3. `#synth` audit commands all resolve (or identify exactly what's missing)
4. Grep for `sorry` — only expected in: continuity of `lmulStarAlgHom` (if needed)
