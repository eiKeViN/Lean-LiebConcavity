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

## Part 3: `starRingEquivStarAlgEquiv_map_cfc` and `op_rpow_eq_rpow_op`

### Step 3a: CFC commutativity for `starRingEquivStarAlgEquiv`

Analogous to `Lmul_map_cfc` in `HStarAlgebra.lean`:

```lean
theorem starRingEquivStarAlgEquiv_map_cfc
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]
    [ContinuousMap.UniqueHom ℝ Aᵐᵒᵖ]
    (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    starRingEquivStarAlgEquiv (cfc f a) = cfc f (starRingEquivStarAlgEquiv a) :=
  starRingEquivStarAlgEquiv.toStarAlgHom.map_cfc _ _ hf
    starRingEquivStarAlgEquiv_continuous ha (ha.map starRingEquivStarAlgEquiv.toStarAlgHom)
```

**Required by `StarAlgHom.map_cfc` (from `Unique.lean:472–479`):**
- `ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` — assumed
- `ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint` — **must be added as hypothesis**
- `ContinuousMap.UniqueHom ℝ Aᵐᵒᵖ` — **must be added as hypothesis**
- `IsScalarTower ℝ ℝ A`, `IsScalarTower ℝ ℝ Aᵐᵒᵖ` — trivial (both from `Algebra.id`)
- `Continuous starRingEquivStarAlgEquiv` — proved (`starRingEquivStarAlgEquiv_continuous`)
- `IsSelfAdjoint (starRingEquivStarAlgEquiv a)` — `ha.map _` (star-alg homs preserve self-adjointness)

**Note on `hφa` simplification:**
`starRingEquivStarAlgEquiv a = op (star a)`. When `ha : IsSelfAdjoint a`, i.e. `star a = a`,
this equals `op a`. Self-adjointness in `Aᵐᵒᵖ`: `star (op a) = op (star a) = op a` ✓.

### Step 3b: `op_rpow_eq_rpow_op`

```lean
lemma op_rpow_eq_rpow_op [IsTopologicalRing A] [T2Space A]
    [ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]
    [ContinuousMap.UniqueHom ℝ Aᵐᵒᵖ] [IsTopologicalRing Aᵐᵒᵖ] [T2Space Aᵐᵒᵖ]
    [NonnegSpectrumClass ℝ Aᵐᵒᵖ]
    {a : A} (ha : 0 ≤ a) (r : ℝ) :
    (op a : Aᵐᵒᵖ) ^ r = op (a ^ r) := by
  rw [rpow_eq_cfc_real (op_nonneg.mpr ha), rpow_eq_cfc_real ha]
  exact (starRingEquivStarAlgEquiv_map_cfc (· ^ r) a).symm
```

Note: `starRingEquivStarAlgEquiv a = op (star a) = op a` when `ha.isSelfAdjoint`.
The `rpow_eq_cfc_real` on `Aᵐᵒᵖ` side needs `[IsTopologicalRing Aᵐᵒᵖ] [T2Space Aᵐᵒᵖ]`.

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

### Step 1: `MulOppositeStarAlgEquiv.lean` — DONE

All of the following are proved and building:
- `starAlgEquiv : A ≃⋆ₐ[ℝ] Aᵐᵒᵖ` (the star-alg equiv `a ↦ op(star a)`)
- `opStar a : Aᵐᵒᵖ` (downstream abbrev)
- `opStar_continuous`, `opStar_isSelfAdjoint`, `opStar_nonneg`, `opStar_eq_op`
- `opStar_map_cfc` (CFC commutativity)
- `opStar_rpow_nonneg`, `opStar_rpow_strictlyPositive`
- `op_rpow_eq_rpow_op_nonneg` (requires `hr : 0 ≤ r`)
- `op_rpow_eq_rpow_op` (strictly positive, no `hr`)

### Step 2: `HStarAlgebra.lean` — discharge `Rmul_rpow_nonneg_op`

Pattern: same as `Lmul_rpow_nonneg`.

```lean
theorem Rmul_rpow_nonneg_op {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (rmulStarAlgHom 𝕜 a) ^ r = rmulStarAlgHom 𝕜 (a ^ r) := by
  symm
  rw [CFC.rpow_eq_cfc_real ha,
      CFC.rpow_eq_cfc_real <| op_nonneg.mpr (Rmul_nonneg 𝕜 ha)]
  exact Rmul_map_cfc 𝕜 (· ^ r) a
```

Note: `rmulStarAlgHom 𝕜 a = op (Rmul 𝕜 a)`, so nonnegativity of `rmulStarAlgHom 𝕜 a`
follows from `op_nonneg.mpr (Rmul_nonneg 𝕜 ha)`.

### Step 3: `HStarAlgebra.lean` — discharge `Rmul_rpow_nonneg`

Use `op_rpow_eq_rpow_op_nonneg` from `MulOppositeStarAlgEquiv.lean` to bridge.

```lean
theorem Rmul_rpow_nonneg {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (Rmul 𝕜 a) ^ r = Rmul 𝕜 (a ^ r) := by
  apply op_injective
  rw [op_rpow_eq_rpow_op_nonneg hr (Rmul_nonneg 𝕜 ha)]
  exact congrArg MulOpposite.unop (Rmul_rpow_nonneg_op 𝕜 hr ha)
```

Need to import `MulOppositeStarAlgEquiv` in `HStarAlgebra.lean`.

---

## Verification

```bash
lake build LeanLiebConcavity.HStarAlgebra
```

Expected: only pre-existing sorries remain; no new sorries.
