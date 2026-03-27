# Plan: Discharge remaining Rmul sorries

## Context

`HStarAlgebra.lean` has three remaining sorries in `section Right`:
1. `Rmul_rpow_nonneg_op` — rpow in `(H →L[𝕜] H)ᵐᵒᵖ` (needs nonnegativity in ᵐᵒᵖ)
2. `Rmul_rpow_nonneg` — rpow in `H →L[𝕜] H` (needs bridge `op(T^r) = (op T)^r`)

The key missing tool is **`starRingEquiv` promoted to a `StarAlgEquiv ℝ A Aᵐᵒᵖ`**,
which would let us apply `StarAlgHom.map_cfc` to transfer CFC across `op`.

## Critical file

`LeanLiebConcavity/HStarAlgebra.lean` — sorries at lines ~453, ~465
`LeanLiebConcavity/ForMathlib.lean` — new lemmas to be added

---

## Part 1: `starRingEquiv` as `StarAlgEquiv ℝ A Aᵐᵒᵖ`

### What exists in Mathlib

| Declaration | Type | File:Line |
|---|---|---|
| `starRingEquiv` | `R ≃+* Rᵐᵒᵖ` | `Algebra/Star/Basic.lean:283` |
| `StarAlgEquiv` structure | extends `StarRingEquiv`, adds `map_smul'` | `Algebra/Star/StarAlgHom.lean:627` |
| `MulOpposite.instAlgebra` | `Algebra R Aᵐᵒᵖ` | `Algebra/Algebra/Opposite.lean:44` |
| `algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c)` | simp lemma | `Algebra/Algebra/Opposite.lean:53` |
| `TrivialStar ℝ` | instance | `Data/Real/Star.lean:21` |
| `op_star : op (star r) = star (op r)` | simp lemma | `Algebra/Star/Basic.lean:533` |
| `StarModule R Mᵐᵒᵖ` | instance | `Algebra/Star/Basic.lean:548` |

### What we need to build (in `ForMathlib.lean`)

**`starRingEquivStarAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ`** (name TBD)

The map `x ↦ op(star x)` is:
- A ring equiv: ✓ (this is `starRingEquiv`)
- Star-preserving: `starRingEquiv(star x) = op(star(star x)) = op(x)` and
  `star(starRingEquiv x) = star(op(star x)) = op(star(star x)) = op(x)` ✓
- Scalar-preserving over ℝ: `starRingEquiv(r • x) = op(star(r • x)) = op(star r • star x)`
  = `op(r • star x)` (since `TrivialStar ℝ` gives `star r = r`)
  = `r • op(star x) = r • starRingEquiv x` ✓

```lean
def starRingEquivStarAlgEquiv [Algebra ℝ A] [StarRing A] [StarModule ℝ A]
    [IsScalarTower ℝ A A] -- or whatever is needed
    : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ :=
  { starRingEquiv with
    map_star' := fun x => by simp [starRingEquiv, op_star]
    map_smul' := fun r x => by simp [starRingEquiv, star_smul, TrivialStar.star_trivial] }
```

### Continuity

`StarAlgHom.map_cfc` requires `Continuous φ`.
`starRingEquivStarAlgEquiv` as a function is `fun x => op (star x)`.
Continuity: `continuous_op.comp continuous_star` (both exist in Mathlib).

---

## Part 2: Order on `Aᵐᵒᵖ`

### What exists in Mathlib

| Declaration | File:Line |
|---|---|
| `PartialOrder αᵐᵒᵖ` (lifted via `unop`) | `Algebra/Order/Group/Opposite.lean:33` |
| `op_nonneg : 0 ≤ op a ↔ 0 ≤ a` | `Algebra/Order/Group/Opposite.lean:57` |
| `StarOrderedRing Rᵐᵒᵖ` | `Algebra/Order/Star/Basic.lean:382` |
| `IsOrderedRing Rᵐᵒᵖ` | `Algebra/Order/Ring/Opposite.lean:24` |
| `CStarRing Eᵐᵒᵖ` | `Analysis/CStarAlgebra/Basic.lean:199` |

### Discharging `0 ≤ rmulStarAlgHom 𝕜 a` from `0 ≤ a`

`rmulStarAlgHom 𝕜 a = op (Rmul 𝕜 a)`. We have `Rmul_nonneg : 0 ≤ a → 0 ≤ Rmul 𝕜 a`.

But the partial order on `(H →L[𝕜] H)ᵐᵒᵖ` is the **lifted order** from `H →L[𝕜] H`
(via `PartialOrder.lift _ unop_injective`), so `0 ≤ op T ↔ 0 ≤ T` by `op_nonneg`.

**However**, the relevant order on `H →L[𝕜] H` for rpow is the **Loewner order**
(`ContinuousLinearMap.instLoewnerPartialOrder`), not the default one. We need to make
sure the PartialOrder on `(H →L[𝕜] H)ᵐᵒᵖ` is indeed the one lifted from Loewner.

If we add `[PartialOrder (H →L[𝕜] H)ᵐᵒᵖ]` as an abstract variable (matching how the
Left section uses `[PartialOrder H]` etc.), this is resolved by assumption.

Alternatively, if the Loewner order is a local instance on `H →L[𝕜] H`, then
`PartialOrder (H →L[𝕜] H)ᵐᵒᵖ` is derived from it automatically.

---

## Part 3: `op_rpow_eq_rpow_op` via `StarAlgHom.map_cfc`

### Key insight

With `φ := starRingEquivStarAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ`, we get from
`StarAlgHom.map_cfc`:

```
φ (cfc f a) = cfc f (φ a)
```

For a **self-adjoint** `a` (where `star a = a`): `φ a = op(star a) = op a`.

So: `op(star(cfc f a)) = cfc f (op a)` in `Aᵐᵒᵖ`.

If furthermore `cfc f a` is self-adjoint (which holds for real-valued CFC on
self-adjoint elements), then `star(cfc f a) = cfc f a`, giving:

```
op(cfc f a) = cfc f (op a)     -- in Aᵐᵒᵖ
```

Applying with `f = (· ^ r)` and using `rpow_eq_cfc_real`:

```
op(a ^ r) = (op a) ^ r         -- for 0 ≤ a self-adjoint
```

This is exactly the bridge lemma needed!

### Proof sketch for `Rmul_rpow_nonneg_op`

```lean
theorem Rmul_rpow_nonneg_op {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    (rmulStarAlgHom 𝕜 a) ^ r = rmulStarAlgHom 𝕜 (a ^ r) := by
  -- rmulStarAlgHom 𝕜 a = op (Rmul 𝕜 a)
  -- 0 ≤ rmulStarAlgHom 𝕜 a follows from Rmul_nonneg + op_nonneg
  have h0 : 0 ≤ rmulStarAlgHom 𝕜 a := op_nonneg.mpr (Rmul_nonneg 𝕜 ha)
  symm
  rw [CFC.rpow_eq_cfc_real ha, CFC.rpow_eq_cfc_real h0]
  exact Rmul_map_cfc 𝕜 (· ^ r) a
```

### Proof sketch for `Rmul_rpow_nonneg`

```lean
theorem Rmul_rpow_nonneg {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    (Rmul 𝕜 a) ^ r = Rmul 𝕜 (a ^ r) := by
  -- Use starRingEquivStarAlgEquiv to bridge: op(T^r) = (op T)^r
  have key : op ((Rmul 𝕜 a) ^ r) = op (Rmul 𝕜 (a ^ r)) := by
    rw [op_rpow_eq_rpow_op ..., Rmul_rpow_nonneg_op ...]
  exact op_injective key
```

Where `op_rpow_eq_rpow_op` is the ForMathlib lemma:
```lean
lemma op_rpow_eq_rpow_op (T : A) (r : ℝ) (hT : 0 ≤ T) :
    op (T ^ r) = (op T : Aᵐᵒᵖ) ^ r
```

---

## Implementation checklist

### Step 1: `ForMathlib.lean` — add `starRingEquivStarAlgEquiv` and `op_rpow_eq_rpow_op`

1. Define `starRingEquivStarAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ` from `starRingEquiv`
   - Need fields: `map_star'` and `map_smul'` (over ℝ)
   - Typeclass requirements: `[Algebra ℝ A] [StarRing A] [StarModule ℝ A]` etc.
2. Prove its continuity: `continuous_op.comp continuous_star`
3. Prove `op_rpow_eq_rpow_op` using `StarAlgHom.map_cfc` applied to `starRingEquivStarAlgEquiv`

### Step 2: `HStarAlgebra.lean` — discharge `Rmul_rpow_nonneg_op`

- Use `op_nonneg.mpr (Rmul_nonneg 𝕜 ha)` for nonnegativity
- Use `Rmul_map_cfc` + `CFC.rpow_eq_cfc_real` (same pattern as `Lmul_rpow_nonneg`)

### Step 3: `HStarAlgebra.lean` — discharge `Rmul_rpow_nonneg`

- Use `op_rpow_eq_rpow_op` + `Rmul_rpow_nonneg_op` + `op_injective`

---

## Verification

```bash
lake build LeanLiebConcavity.HStarAlgebra
```

Expected: only pre-existing sorries remain; no new sorries.
