# Rmul: CFC commutation and rpow

## Status (2026-03-27)

Parts A–C are **done** in `HStarAlgebra.lean`:
- `Rmul_isSymmetric`, `re_inner_Rmul_star_mul_self_nonneg`
- `Rmul_isPositive`, `Rmul_nonneg`
- `Rmul_star`, `rmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ`
- `Rmul_isSelfAdjoint`

Remaining: **Parts D and E** — `Rmul_map_cfc` and `Rmul_rpow_nonneg`.

---

## Mathlib infrastructure (confirmed)

| What | Status | Location |
|------|--------|----------|
| `NormedRing Rᵐᵒᵖ` | ✓ | `Analysis/Normed/Ring/Basic.lean:521` |
| `NormedAlgebra 𝕜 Eᵐᵒᵖ` | ✓ | `Analysis/Normed/Module/Basic.lean:387` |
| `CStarRing Eᵐᵒᵖ` | ✓ | `Analysis/CStarAlgebra/Basic.lean:199` |
| `starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E` | ✓ | `Analysis/CStarAlgebra/Basic.lean:294` |
| `starRingEquiv : R ≃+* Rᵐᵒᵖ` (x ↦ op(star x)) | ✓ | `Algebra/Star/Basic.lean:283` |
| `StarAlgHom.map_cfc` | ✓ | `ContinuousFunctionalCalculus/Unique.lean:508` |
| `ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint` | ✗ not in Mathlib | — |

---

## Part D: `Rmul_map_cfc` (in `namespace CFC`, needs new variables)

### Strategy

`rmulStarAlgHom : H →⋆ₐ[𝕜] (H →L[𝕜] H)ᵐᵒᵖ` is already defined.
Apply `StarAlgHom.map_cfc` to it, exactly mirroring `Lmul_map_cfc`.

This requires CFC on `(H →L[𝕜] H)ᵐᵒᵖ`, which is NOT in Mathlib as a derived instance,
so we add it as an abstract variable (acceptable since our typeclass stack is already
abstract).

### New variables to add (alongside the existing `(H →L[𝕜] H)` variables)

```lean
variable [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H)ᵐᵒᵖ IsSelfAdjoint]
variable [ContinuousMap.UniqueHom ℝ (H →L[𝕜] H)ᵐᵒᵖ]
variable [StarOrderedRing (H →L[𝕜] H)ᵐᵒᵖ]
variable [NonnegSpectrumClass ℝ (H →L[𝕜] H)ᵐᵒᵖ]
```

(User confirmed experimentally that adding these compiles.)

### `rmul_continuous_op`

Needed for `StarAlgHom.map_cfc`'s continuity hypothesis:

```lean
theorem rmul_continuous_op :
    Continuous (rmulStarAlgHom 𝕜 : H → (H →L[𝕜] H)ᵐᵒᵖ) :=
  continuous_op.comp (rmul_continuous 𝕜)
```

(`continuous_op : Continuous (MulOpposite.op : A → Aᵐᵒᵖ)` is in Mathlib.)

### `Rmul_isSelfAdjoint_op`

Self-adjointness of `op (Rmul 𝕜 a)` in `(H →L[𝕜] H)ᵐᵒᵖ` when `IsSelfAdjoint a`.
Star on `Aᵐᵒᵖ` is `star(op x) = op(star x)`, so:

```lean
lemma Rmul_isSelfAdjoint_op {a : H} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (rmulStarAlgHom 𝕜 a) := by
  simp only [IsSelfAdjoint, rmulStarAlgHom, StarAlgHom.coe_mk, AlgHom.coe_mk]
  -- goal: star (op (Rmul 𝕜 a)) = op (Rmul 𝕜 a)
  -- star on Aᵐᵒᵖ: star(op x) = op(star x)
  simp [MulOpposite.star_def, Rmul_star, (Rmul_isSelfAdjoint 𝕜 ha).star_eq]
```

(Exact simp lemmas TBD; may use `ha.map (rmulStarAlgHom 𝕜)` directly if that typeclass
path works.)

### `Rmul_map_cfc`

```lean
theorem Rmul_map_cfc (f : ℝ → ℝ) (a : H)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    rmulStarAlgHom 𝕜 (cfc f a) = cfc f (rmulStarAlgHom 𝕜 a) :=
  (rmulStarAlgHom 𝕜).map_cfc _ _ hf (rmulStarAlgHom_continuous 𝕜) ha
    (ha.map (rmulStarAlgHom 𝕜))
```

Result lives in `(H →L[𝕜] H)ᵐᵒᵖ`:
`op (Rmul 𝕜 (cfc f a)) = cfc f (op (Rmul 𝕜 a))`.

---

## Part E: `Rmul_rpow_nonneg`

### The missing bridge: `op_rpow_eq_rpow_op`

To extract `(Rmul 𝕜 a)^r = Rmul 𝕜 (a^r)` in `H →L[𝕜] H` from `Rmul_map_cfc`,
we need:

```lean
-- For self-adjoint T : A, (op T : Aᵐᵒᵖ)^r = op (T^r : A)
lemma op_rpow_eq_rpow_op {T : H →L[𝕜] H} (hT : 0 ≤ T) (r : ℝ) :
    (MulOpposite.op T : (H →L[𝕜] H)ᵐᵒᵖ) ^ r = MulOpposite.op (T ^ r) := ...
```

**Why this holds**: `op ∘ star : A →⋆ₐ[ℝ] Aᵐᵒᵖ` is a star-algebra hom over ℝ
(because `star` is a ring anti-hom and `op` reverses multiplication, so the
composition `op ∘ star` is a genuine ring hom into `Aᵐᵒᵖ`). On self-adjoint elements
`star T = T`, so `(op ∘ star)(T) = op T`. By `StarAlgHom.map_cfc`:
`(op ∘ star)(T^r) = ((op ∘ star)(T))^r`, i.e., `op(T^r) = (op T)^r`.

**Mathlib gap**: `starRingEquiv : R ≃+* Rᵐᵒᵖ` (x ↦ op(star x)) is only a ring equiv,
not packaged as a `StarAlgHom`. Promoting it to `StarAlgHom` over ℝ is a
`ForMathlib` item.

**Plan**: sorry `op_rpow_eq_rpow_op` with a clear TODO comment for `ForMathlib`.

### `Rmul_rpow_nonneg`

```lean
/-- Right multiplication commutes with nonneg real powers: `(R_a)^r = R_{a^r}`. -/
theorem Rmul_rpow_nonneg {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (Rmul 𝕜 a) ^ r = Rmul 𝕜 (a ^ r) := by
  have hRa : 0 ≤ Rmul 𝕜 a := Rmul_nonneg 𝕜 ha
  -- Use Rmul_map_cfc in (H →L[𝕜] H)ᵐᵒᵖ:
  -- op(Rmul 𝕜 (cfc (·^r) a)) = cfc (·^r) (op (Rmul 𝕜 a))
  have key := Rmul_map_cfc 𝕜 (· ^ r) a
  -- LHS: cfc (·^r) (op (Rmul 𝕜 a)) = op((Rmul 𝕜 a)^r)  [by op_rpow_eq_rpow_op]
  -- RHS: op(Rmul 𝕜 (a^r))  [by CFC.rpow_eq_cfc_real on H side]
  rw [← CFC.rpow_eq_cfc_real ha] at key
  rw [← op_rpow_eq_rpow_op hRa r, ← key]
  simp [CFC.rpow_eq_cfc_real hRa]
```

(Exact proof term TBD depending on `op_rpow_eq_rpow_op` form; the outline is correct.)

Also add the strictly-positive and apply variants mirroring `Lmul_rpow_strictlyPositive`.

---

## Implementation checklist

- [ ] Add `rmulStarAlgHom_continuous` (near other continuity lemmas)
- [ ] Add new variables to `namespace CFC` section for `(H →L[𝕜] H)ᵐᵒᵖ`
- [ ] Add `Rmul_map_cfc`
- [ ] Add `op_rpow_eq_rpow_op` (sorry, ForMathlib TODO) in `ForMathlib.lean`
- [ ] Add `Rmul_rpow_nonneg`, `Rmul_rpow_strictlyPositive` and apply variants

## Verification

```bash
lake build LeanLiebConcavity.HStarAlgebra
```

Expected: sorries only in `op_rpow_eq_rpow_op` and the `Rmul_rpow` theorems.
