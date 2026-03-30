# Plan: Generalize `isStrictlyPositive_convex_comb` and Prove Lieb's Theorem

## Context

`Lieb.lean` proves `OperatorPowerMean_jointly_concave` / `OperatorPowerMean_jointly_convex`
for `H : HStarAlgebra ℂ H`. The proof of `convex_sp_nonneg` uses
`isStrictlyPositive_convex_comb` from `ForMathlib.lean`, which currently requires
`[CStarAlgebra A]`. But `H` only has `[HStarAlgebra ℂ H]`, causing a timeout.

---

## Root Cause Analysis

Dependency chain:
```
isStrictlyPositive_convex_comb
  → IsStrictlyPositive.add_nonneg
  → IsStrictlyPositive.of_le
  → CStarAlgebra.isUnit_of_le        ← bottleneck
  → CFC.exists_pos_algebraMap_le_iff ← already explicit typeclasses!
```

`CFC.exists_pos_algebraMap_le_iff` (Mathlib `Order.lean` lines 137–148) takes explicit typeclasses:
```lean
[TopologicalSpace A] [Ring A] [StarRing A]
[PartialOrder A] [StarOrderedRing A] [Algebra ℝ A]
[NonnegSpectrumClass ℝ A] [Nontrivial A]
[ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
```

**The `[CStarAlgebra A]` in Mathlib's `CStarAlgebra.isUnit_of_le` is purely a section
variable, not a logical requirement.** The proof body uses only `CFC.exists_pos_algebraMap_le_iff`.

---

## Fix Plan

### A. Generalize `ForMathlib.lean`

Change the `section StrictPositivity` variable block from:
```lean
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
```
to:
```lean
variable {A : Type*} [TopologicalSpace A] [NormedRing A] [StarRing A]
  [Algebra ℝ A] [NormedAlgebra ℝ A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
```

Add `isUnit_of_le_general` (identical proof body to `CStarAlgebra.isUnit_of_le`):
```lean
lemma isUnit_of_le_general (a : A) {b : A} (hab : a ≤ b)
    (h : IsStrictlyPositive a := by cfc_tac) : IsUnit b := by
  have h₀ := h.isUnit
  have ha := h.nonneg
  rw [← spectrum.zero_notMem_iff ℝ≥0] at h₀ ⊢
  nontriviality A
  have hb := (show 0 ≤ a from ha).trans hab
  rw [zero_notMem_iff, SpectrumRestricts.nnreal_lt_iff (.nnreal_of_nonneg ‹_›),
    NNReal.coe_zero, ← CFC.exists_pos_algebraMap_le_iff (.of_nonneg ‹_›)] at h₀ ⊢
  peel h₀ with r hr _
  exact this.trans hab
```

Update `IsStrictlyPositive.of_le` (if local) and `isStrictlyPositive_convex_comb` to call
`isUnit_of_le_general` instead of `CStarAlgebra.isUnit_of_le`.

**Verify**: `HStarAlgebra ℂ H` provides `NormedRing H`, `StarRing H`, `Algebra ℂ H` (hence
`Algebra ℝ H`), `NormedAlgebra ℝ H`. The `Lieb.lean` variable block adds
`[NonnegSpectrumClass ℝ H]` and `[ContinuousFunctionalCalculus ℝ H IsSelfAdjoint]`. ✓

### B. Fix ℝ-vs-ℂ scalar issue in `Lieb.lean` Step 3

`Lmul_smul` and `Rmul_smul` are `𝕜`-scalar lemmas (complex), not ℝ-scalar.
The `Prod.smul` in the concavity proof uses `ℝ`-scalars.

Options:
- Use `map_smul` with the coercion `ℝ → ℂ` to convert ℝ-smul to ℂ-smul
- Or unfold `Prod.smul` manually and use `ContinuousLinearMap.smul_apply`

---

## Remaining Steps for `Lieb.lean`

### Step 4 — `LiebConcavity_inner`
```lean
theorem LiebConcavity_inner {α β : ℝ} (hα : 0 < α ∧ α ≤ 1) (hβ : 0 < β ∧ β ≤ 1) (x : H) :
    ConcaveOn ℝ {p : H × H | IsStrictlyPositive p.1 ∧ 0 ≤ p.2}
      (fun p => RCLike.re ⟪OperatorPowerMean α β p.1 p.2 x, x⟫_ℂ) := by
  -- T ↦ re ⟪T x, x⟫ is ℝ-linear → apply ConcaveOn.comp with linear map
  apply (OperatorPowerMean_jointly_concave hα hβ).inner_right
```

### Step 5 — `LiebConcavity` (parameter correspondence)
Set `α = t`, `β = s + t`, so `β*(1-α) = (s+t)*(1-t/(s+t))*(s+t)/(s+t) = s`.
More cleanly: set `β = s+t`, `α = t/(s+t)`:
- `β*(1-α) = (s+t)*s/(s+t) = s` ✓
- `α = t/(s+t) ∈ (0,1]` since `t > 0`, `s+t ≤ 1` ✓
- `β = s+t ∈ (0,1]` since `s,t > 0` and `s+t ≤ 1` ✓

### Step 6 — sorry-stubs
- `LiebExtension`: special case `s = t = q/2`
- `AndoConvexity`: convex version, `1 ≤ α ≤ 2`, `0 < β ≤ 1`
- `Corollary_1_3` of [Nik2013]

---

## Key Mathlib References

| Lemma | File | Line |
|-------|------|------|
| `CFC.exists_pos_algebraMap_le_iff` | `CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` | 137 |
| `CStarAlgebra.isUnit_of_le` | same | 283 |
| `IsStrictlyPositive.add_nonneg` | same | 389 |
| `SpectrumRestricts.nnreal_of_nonneg` | `Analysis/Real/Spectrum.lean` | ~30 |
| `SpectrumRestricts.nnreal_lt_iff` | same | ~41 |
