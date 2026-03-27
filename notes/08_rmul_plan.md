# Rmul: Symmetry, Positivity, Star, and Rpow

## Context

Build the Rmul analogs of the Lmul results in `LeanLiebConcavity/HStarAlgebra.lean`.
**UPDATED 2026-03-27**: The MulOpposite approach for `Rmul_rpow` is NOW VIABLE in principle—
Mathlib HAS `NormedRing Rᵐᵒᵖ`, `NormedAlgebra 𝕜 Eᵐᵒᵖ`, and `CStarRing Eᵐᵒᵖ`.
The sole remaining blocker: **no `ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint` instance** in Mathlib.

## Mathlib MulOpposite and CFC infrastructure (UPDATED)

| What | Status | Location | Notes |
|------|--------|----------|-------|
| `StarRing Rᵐᵒᵖ` | ✓ yes | `Algebra/Star/Basic.lean:545` | star(op(a)) = op(star(a)) |
| `starRingEquiv : R ≃+* Rᵐᵒᵖ` | ✓ yes | `Algebra/Star/Basic.lean:283` | ring iso via star composition |
| `NonUnitalNormedRing Rᵐᵒᵖ` | ✓ yes | `Analysis/Normed/Ring/Basic.lean:497` | **was missing, now found** |
| `NormedRing Rᵐᵒᵖ` | ✓ yes | `Analysis/Normed/Ring/Basic.lean:521` | **CORRECTED: was "no", actually YES** |
| `NormedAlgebra 𝕜 Eᵐᵒᵖ` | ✓ yes | `Analysis/Normed/Module/Basic.lean:387` | **CORRECTED: was "no", actually YES** |
| `CStarRing Eᵐᵒᵖ` | ✓ yes | `Analysis/CStarAlgebra/Basic.lean:199` | `‖x⋆*x‖ = ‖x*x⋆‖` (conjugate norm) |
| `ContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint` | ✗ **BLOCKER** | not in Mathlib | Spectrum/CFC transfer to opposite missing |
| `AlgEquiv.op`, `.opComm` | ✓ yes | `Algebra/Algebra/Opposite.lean:141,169` | Convert `A ≃ₐ Bᵐᵒᵖ` ↔ `Aᵐᵒᵖ ≃ₐ B` |
| `StarAlgHom.map_cfc` | ✓ yes | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean:508` | **KEY**: CFC commutes with star-alg homs |
| `IsSelfAdjoint.map_spectrum_real` | ✓ yes | `Analysis/CStarAlgebra/Hom.lean:24–27` | Injective star-alg hom preserves real spectrum |

## Alternative approaches for `Rmul_rpow_nonneg`

### **Approach 1: MulOpposite + CFC (Best if CFC instance added)**

**Goal**: Define `rmulStarAlgHom : Hᵐᵒᵖ →⋆ₐ[𝕜] B(H)` and apply `StarAlgHom.map_cfc`.

**Status**: ALMOST VIABLE
- `fun x ↦ Rmul 𝕜 (unop x)` is a ring anti-hom (Rmul is anti-hom)
- Composing with `op : H → Hᵐᵒᵖ` gives a ring hom from `Hᵐᵒᵖ`
- It preserves star (via `Rmul_star` lemma)
- **Missing piece**: `ContinuousFunctionalCalculus ℝ Hᵐᵒᵖ IsSelfAdjoint` instance
  - Should follow from: spectrum of `op a` in `Hᵐᵒᵖ` = spectrum of `a` in `H` (isomorphic algebras)
  - Lemma `IsSelfAdjoint.map_spectrum_real` shows injective star-alg homs preserve spectrum

### **Approach 2: Direct Conjugation by `starₗᵢ` (Viable Now)**

**Goal**: Use `Rmul_eq_star_Lmul_star` + conjugation by `starₗᵢ : H ≃ₗᵢ⋆[𝕜] H`.

**Status**: PROMISING (needs verification of star/adjoint compatibility)

**Strategy**:
- `Rmul 𝕜 a = starₗᵢ ∘ Lmul 𝕜 (star a) ∘ starₗᵢ` (identity already proven in project)
- For `a ≥ 0`: `star a = a`, so `Rmul 𝕜 a = starₗᵢ ∘ Lmul 𝕜 a ∘ starₗᵢ`
- Key claim: Conjugation by `starₗᵢ` (restricted to ℝ-linearity) is a C*-algebra aut of `B_ℝ(H)`
- Then: `(Rmul 𝕜 a)^r = starₗᵢ ∘ (Lmul 𝕜 a)^r ∘ starₗᵢ = starₗᵢ ∘ Lmul 𝕜 (a^r) ∘ starₗᵢ = Rmul 𝕜 (a^r)`

**Available tools**:
- `starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E` — semilinear isometric equiv (in `Analysis/CStarAlgebra/Basic.lean:294`)
- `starL 𝕜 : E ≃L⋆[𝕜] E` — continuous linear equiv (in `Basic.lean:307`)
- `ContinuousLinearMap.star_eq_adjoint` — relates star on CLM to adjoint

**Potential issue**: Need to verify `adj(starₗᵢ ∘ T ∘ starₗᵢ) = starₗᵢ ∘ adj(T) ∘ starₗᵢ` for the CFC to transfer via conjugation.

### **Approach 3: Spectrum Identity + Uniqueness (Fallback)**

**Goal**: Prove spectrum of `Rmul 𝕜 a` = spectrum of `Lmul 𝕜 a` (up to ordering).

**Status**: POSSIBLE but complex
- Use HStarAlgebra norm properties to relate operators in `B(H)`
- Apply `cfc_le_iff` or CFC uniqueness lemma to compare `(Rmul 𝕜 a)^r` and `Rmul 𝕜 (a^r)`

## Implementation plan

### Part A: Rmul prerequisites (no CompleteSpace needed)

Place after `Lmul_isSymmetric` / `re_inner_Lmul_star_mul_self_nonneg` block (around line 207).

**1. `Rmul_isSymmetric`** — mirror of `Lmul_isSymmetric`
```lean
theorem Rmul_isSymmetric {a : H} (ha : IsSelfAdjoint a) :
    LinearMap.IsSymmetric (Rmul 𝕜 a).toLinearMap :=
  fun x y => by
    change ⟪x * a, y⟫ = ⟪x, y * a⟫
    rw [inner_mul_left_eq, ha.star_eq]
```

**2. `re_inner_Rmul_star_mul_self_nonneg`** — base case for positivity
```lean
theorem re_inner_Rmul_star_mul_self_nonneg (s x : H) :
    0 ≤ RCLike.re ⟪(Rmul 𝕜 (star s * s)) x, x⟫ := by
  simp_rw [Rmul_apply, mul_assoc]
  -- ⟪(x * star s) * s, x⟫ = ⟪x * star s, x * star s⟫
  rw [inner_mul_left_eq, star_star]
  exact inner_self_nonneg
```

### Part B: Rmul positivity (in `section StarAlgHom`, needs `[PartialOrder H] [StarOrderedRing H]`)

**3. `Rmul_isPositive`** — closure induction, same pattern as `Lmul_isPositive`
```lean
omit [CompleteSpace H] in
theorem Rmul_isPositive {a : H} (ha : 0 ≤ a) : (Rmul 𝕜 a).IsPositive := by
  refine ⟨Rmul_isSymmetric 𝕜 (IsSelfAdjoint.of_nonneg ha), fun x => ?_⟩
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem b hb =>
    obtain ⟨s, rfl⟩ := hb
    exact re_inner_Rmul_star_mul_self_nonneg 𝕜 s x
  | zero => simp
  | add b c _ _ ihb ihc =>
    rw [Rmul_add, ContinuousLinearMap.add_apply, inner_add_left, map_add RCLike.re]
    exact add_nonneg ihb ihc
```

Wait — `Rmul_add` has signature `Rmul 𝕜 a + Rmul 𝕜 b = Rmul 𝕜 (a + b)`, direction
is reversed from what we need. May need `(Rmul_add).symm` or `← Rmul_add`.

**4. `Rmul_nonneg`** — bridge to Loewner order
```lean
attribute [local instance] ContinuousLinearMap.instLoewnerPartialOrder
omit [CompleteSpace H] in
theorem Rmul_nonneg {a : H} (ha : 0 ≤ a) : 0 ≤ Rmul 𝕜 a := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive (Rmul 𝕜 a)]
  exact Rmul_isPositive 𝕜 ha
```

### Part C: Rmul star (in `section StarAlgHom`, needs CompleteSpace)

**5. `Rmul_star`** — mirror of `Lmul_star`
```lean
theorem Rmul_star (a : H) :
    Rmul 𝕜 (star a) = star (Rmul 𝕜 a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    simp only [Rmul_apply, inner_mul_left_eq, star_star]
```

### Part D: Rmul rpow (in `section CFC`) — sorry

**6. `Rmul_rpow_nonneg`** — sorry with TODO comment.

The MulOpposite route is blocked (no CFC/NormedRing on `Aᵐᵒᵖ`).
Alternative approaches for future:
- Build `HStarAlgebra 𝕜 Hᵐᵒᵖ` instance + transfer
- Direct CFC anti-hom argument
- Conjugation: `R_a = star . L_{a*} . star` (pointwise identity, hard to lift to operator rpow)

```lean
/-- Right multiplication commutes with nonneg real powers: `(R_a)^r = R_{a^r}`.
TODO: prove via MulOpposite approach once CFC on Aᵐᵒᵖ is available in Mathlib,
or by building HStarAlgebra 𝕜 Hᵐᵒᵖ. -/
theorem Rmul_rpow_nonneg {r : ℝ} {a : H} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    (Rmul 𝕜 a) ^ r = Rmul 𝕜 (a ^ r) := by
  sorry
```

## Verification

```bash
lake build LeanLiebConcavity.HStarAlgebra
```

Expected: pre-existing sorry in `nonneg_decompose` + new sorry in `Rmul_rpow_nonneg`.
