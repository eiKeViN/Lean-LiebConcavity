# H*-Algebra Left Multiplication: Positivity & CFC Commutation

## Completed Implementation

This note documents the completion of Step 3 of the lmulStarAlgHom plan: adding `Lmul_isSelfAdjoint`, `Lmul_isPositive`, and `Lmul_map_cfc` to `LeanLiebConcavity/HStarAlgebra.lean`.

---

## 1. Self-Adjointness Preservation: `Lmul_isSelfAdjoint`

**Signature:**
```lean
theorem Lmul_isSelfAdjoint {a : H} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (lmulStarAlgHom 𝕜 a)
```

**Proof:**
Uses `IsSelfAdjoint.map` from Mathlib (`Algebra/Star/SelfAdjoint.lean:98`):
```lean
  ha.map (lmulStarAlgHom 𝕜)
```

**How it works:**
- `lmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H)` is a `StarAlgHom`, hence carries `StarHomClass` instance
- `IsSelfAdjoint.map` applies any star homomorphism to a self-adjoint element and preserves self-adjointness
- For CLMs, `IsSelfAdjoint (Lmul 𝕜 a)` means `star (Lmul 𝕜 a) = Lmul 𝕜 a` (via adjoint equivalence)

**Location:** `section StarAlgHom` (requires `[CompleteSpace H]` for `lmulStarAlgHom`)

---

## 2. Positivity of Left Multiplication: `Lmul_isPositive`

**Signature:**
```lean
theorem Lmul_isPositive {a : H} (ha : 0 ≤ a) : (Lmul 𝕜 a).IsPositive
```

**Definition of `ContinuousLinearMap.IsPositive`** (from `Analysis/InnerProductSpace/Positive.lean:273–274`):
```lean
def IsPositive (T : E →L[𝕜] E) : Prop :=
  T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x
```

where `T.reApplyInnerSelf x := re ⟪T x, x⟫` (real inner product).

**Proof Structure:**
```lean
refine ⟨Lmul_isSymmetric 𝕜 (IsSelfAdjoint.of_nonneg ha), fun x => ?_⟩
-- First component: T.IsSymmetric — established by Lmul_isSymmetric
-- Second component: ∀ x, 0 ≤ re ⟪(Lmul 𝕜 a) x, x⟫ — by induction on closure
```

**Key lemmas used:**
- `Lmul_isSymmetric`: if `a` is self-adjoint, `Lmul a` is a symmetric operator
- `IsSelfAdjoint.of_nonneg`: nonneg elements are self-adjoint (in `StarOrderedRing`)
- `re_inner_Lmul_star_mul_self_nonneg`: base case for nonneg decomposition
- `AddSubmonoid.closure_induction`: induction on `a ∈ closure (Set.range (star · * ·))`
  - **Mem case**: `a = star s * s` directly yields nonnegativity via `re_inner_Lmul_star_mul_self_nonneg`
  - **Zero case**: `re ⟪L_0 x, x⟫ = 0` (simp)
  - **Add case**: `re ⟪(L_b + L_c) x, x⟫ = re ⟪L_b x, x⟫ + re ⟪L_c x, x⟫` (via `Lmul_add` and `map_add RCLike.re`)

**Location:** `section StarAlgHom` (requires `[CompleteSpace H]`)

**Important:** Depends on `[PartialOrder H]` and `[StarOrderedRing H]` (outer scope from line 235 onward)

---

## 3. CFC Commutation: `Lmul_map_cfc`

**Signature:**
```lean
theorem Lmul_map_cfc (f : ℝ → ℝ) (a : H)
    (hφ : Continuous (lmulStarAlgHom 𝕜 : H → H →L[𝕜] H))
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    lmulStarAlgHom 𝕜 (cfc f a) = cfc f (lmulStarAlgHom 𝕜 a)
```

**Proof:**
Direct application of `StarAlgHom.map_cfc` from Mathlib:
```lean
  StarAlgHom.map_cfc (lmulStarAlgHom 𝕜) f a hf hφ ha (Lmul_isSelfAdjoint ha)
```

**Key design decisions:**

1. **Explicit continuity hypothesis `hφ`**:
   - `IsTopologicalSemiring H` only guarantees pointwise continuity of each `L_a` (i.e., `x ↦ a * x`)
   - It does NOT guarantee that the map `a ↦ L_a : H → (H →L[𝕜] H)` is continuous in the operator norm
   - A submultiplicative norm (from `NormedAlgebra`) would give this, but `HStarAlgebra` doesn't require it
   - **Callers can discharge `hφ` when `H` is finite-dimensional or has `NormedAlgebra` structure**

2. **Scalar tower variables:**
   - `[Algebra ℝ H]` — needed for `spectrum ℝ a`
   - `[IsScalarTower ℝ 𝕜 H]` — required by `StarAlgHom.map_cfc`'s variable block
   - `[IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]` — for the codomain
   - Must be declared **before** CFC instances, as they depend on scalar towers

3. **CFC on codomain `H →L[𝕜] H`:**
   - Declared as `variable [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]`
   - When `𝕜 = ℂ`, this auto-synthesizes from `CStarAlgebra (H →L[ℂ] H)` (from Mathlib)
   - For abstract `𝕜`, may need explicit instantiation

4. **`Lmul_isSelfAdjoint` integration:**
   - The last hypothesis to `map_cfc` is `hφa : q (φ a)` (codomain self-adjointness)
   - We provide it as `Lmul_isSelfAdjoint ha` — direct application of the lemma above

**Location:** New `section CFC` after `end StarAlgHom` (requires `[CompleteSpace H]`)

---

## 4. Implementation Highlights

### Typeclass Changes

Changed class definition from:
```lean
class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] extends
    NormedAddCommGroup H, Semiring H, ...
```

to:
```lean
class HStarAlgebra (𝕜 : Type*) (H : Type*) [RCLike 𝕜] extends
    NormedAddCommGroup H, Ring H, ...
```

**Rationale:** `ContinuousFunctionalCalculus` requires `[Ring A]` for spectrum/nonneg to make sense. `Ring` extends `Semiring`, so the change is backwards-compatible.

### Import Additions

```lean
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
```

The second import provides `StarAlgHom.map_cfc`. The first provides `ContinuousLinearMap.IsPositive` and related infrastructure.

### Proof Techniques

**Induction over closure:**
```lean
induction ha using AddSubmonoid.closure_induction with
| mem b hb => ...
| zero => ...
| add b c _ _ ihb ihc => ...
```

This pattern is standard for Mathlib in Lean 4. The `motive` is implicit and derived from the goal.

---

## 5. Related Mathlib Declarations

| Name | File | Purpose |
|------|------|---------|
| `IsSelfAdjoint.map` | `Algebra/Star/SelfAdjoint.lean:98` | Preserve self-adjointness under star homs |
| `ContinuousLinearMap.IsPositive` | `Analysis/InnerProductSpace/Positive.lean:273` | Definition of positive operator |
| `ContinuousLinearMap.reApplyInnerSelf` | `Analysis/InnerProductSpace/LinearMap.lean:270` | Real-valued inner product `re ⟪T x, x⟫` |
| `StarAlgHom.map_cfc` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean:508` | CFC commutation for star alg homs |
| `AddSubmonoid.closure_induction` | `Algebra/Group/Submonoid/Basic.lean:162` | Induction principle for closure |

---

## 6. Remaining Work

**Continuity of `lmulStarAlgHom`:**
- Currently passed as an explicit hypothesis `hφ` to `Lmul_map_cfc`
- Can be discharged:
  - For finite-dimensional `H`: all linear maps are continuous
  - If `H` carries `NormedAlgebra 𝕜 H`: the operator norm bound `‖L_a‖_op ≤ ‖a‖` follows from `norm_mul_le`
  - Manually in specific instantiations

**CFC on `H`:**
- Currently assumed via `variable [ContinuousFunctionalCalculus ℝ H IsSelfAdjoint]`
- In the full project, this would be proven by constructing CFC on the concrete H*-algebra (e.g., finite-dimensional matrices or a concrete Hilbert space)

---

## 7. Verification

File compiles without error (only pre-existing `sorry` in `nonneg_decompose`):
```
lake build LeanLiebConcavity.HStarAlgebra
```

All three theorems are complete and proven.
