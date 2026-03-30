# Mathlib Key Paths — Lean-LiebConcavity

Living table of key Mathlib file paths for this project, grouped by topic.
All paths are relative to `.lake/packages/mathlib/Mathlib/`.

> **Canonical copy** is the memory file at
> `~/.claude/projects/.../memory/mathlib_key_paths.md`.
> This copy is kept in sync by `/update`. Edit the memory copy, then re-run `/update`.

---

## CFC — Continuous Functional Calculus

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| `cfc_nonneg`, `cfc_nonneg_iff` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 929, 951 |
| `cfc_inv`, `cfc_zpow`, `CFC.inv_nonneg_of_nonneg` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 781, 832, 1011 |
| `CStarAlgebra.instNonnegSpectrumClass` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean` | 351 |
| **`StarAlgHomClass.map_cfc`** — CFC commutes with star-algebra homs; `φ(cfc f a) = cfc f (φ a)` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean` | 483–486 |
| **Hypotheses for `StarAlgHomClass.map_cfc`**: `[AlgHomClass F S A B]`, `[StarHomClass F A B]`, `hφ : Continuous φ` (explicit, auto-tactic), requires CFC on both domain and codomain, `ContinuousMap.UniqueHom` on codomain | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean` | 483–486 |
| `NonUnitalStarAlgHomClass.map_cfcₙ` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean` | ~434 |
| Order lemmas (`cfc_le_cfc`, `conjugate_nonneg_of_nonneg`, etc.) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` | various |
| `rpow` definition, `rpow_nonneg` | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 408, 419 |
| `CFC.sqrt_eq_rpow`, `CFC.sqrt_mul_sqrt_self` | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | various |
| **`cfc_map_spectrum`** (spectral mapping theorem) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 390 |
| **`cfc_isStrictlyPositive_iff`** (strictly positive on spectrum) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 940 |
| **`StarOrderedRing.isStrictlyPositive_iff_spectrum_pos`** (element strictly positive iff spectrum positive) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 946 |
| `cfc_nonneg_iff` (nonneg characterization via spectrum) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 929 |
| `cfc_mono` (monotonicity of CFC) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 920 |
| `NonnegSpectrumClass` (typeclass for spectrum nonnegativity) | `Algebra/Algebra/Spectrum/Quasispectrum.lean` | 394 |

### CFC Commutativity (Element Commutativity)

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`Commute.cfcHom`** — If `Commute a b` and `Commute (star a) b`, then `Commute (cfcHom ha f) b` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | 45 |
| **`IsSelfAdjoint.commute_cfcHom`** — Simplified: for self-adjoint `a`, if `Commute a b` then `Commute (cfcHom ha f) b` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | 66 |
| **`Commute.cfc`** — If `Commute a b` and `Commute (star a) b`, then `Commute (cfc f a) b` (general form) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | 76 |
| **`IsSelfAdjoint.commute_cfc`** — For self-adjoint `a`: if `Commute a b` then `Commute (cfc f a) b` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | 86 |
| **`Commute.cfc_real`** — Real-valued CFC: if `Commute a b` then `Commute (cfc f a) b` for `f : ℝ → ℝ` (avoids star requirement) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | 101 |
| **`Commute.cfc_nnreal`** — Non-negative real CFC: if `Commute a b` then `Commute (cfc f a) b` for `f : ℝ≥0 → ℝ≥0` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean` | 112 |
| **`cfc_commute_cfc`** — **KEY**: For any element `a` and any functions `f, g`, we have `Commute (cfc f a) (cfc g a)` (different functions on same element commute!) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 377 |
| **`cfcₙ_commute_cfcₙ`** — Non-unital version: `Commute (cfcₙ f a) (cfcₙ g a)` for any `f, g` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.lean` | 299 |
| **`rpow_def`** — `a ^ y = cfc (fun x : ℝ≥0 => x ^ y) a`; junk value is 0 when `¬ (0 ≤ a)` | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 423 |
| **`cfc_cases`** — reduces goal `P (cfc f a)` to `P 0` (junk) and the honest case | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 366 |

### ForMathlib additions (this project)

| Declaration | File | Notes |
|-------------|------|-------|
| `Commute.cfc_cfc_real` — `Commute a b → Commute (cfc f a) (cfc g b)` for `f g : ℝ → ℝ` | `ForMathlib.lean` | No star hypotheses needed |
| `Commute.rpow_right` — `Commute a b → Commute a (b ^ r)` | `ForMathlib.lean` | No nonnegativity needed; uses `rpow_def` + `cfc_nnreal` |
| `Commute.rpow_left` — `Commute a b → Commute (a ^ r) b` | `ForMathlib.lean` | Derived from `rpow_right` |
| `Commute.rpow_rpow` — `Commute a b → Commute (a ^ r) (b ^ s)` | `ForMathlib.lean` | Unconditional |
| `cfc_isStrictlyPositive_of_pos` — `IsStrictlyPositive a → (∀ x > 0, 0 < f x) → ContinuousOn f σ(a) → IsStrictlyPositive (cfc f a)` | `ForMathlib.lean` | Maps strictly positive through CFC |
| `cfc_isStrictlyPositive_of_nonneg` — Same as above but works on `[0, ∞)` for nonneg element | `ForMathlib.lean` | Extends strict positivity condition |
| `rpow_continuousOn_pos` — `ContinuousOn (·^r : ℝ → ℝ) (Ioi 0)` (available for all `r : ℝ`) | `ForMathlib.lean` | Works for negative exponents (vs `continuous_rpow_const`) |
| `mul_rpow_of_commute` — `Commute a b → 0 ≤ a → 0 ≤ b → (a * b) ^ r = a ^ r * b ^ r` | `ForMathlib.lean` | **SORRIED** — requires two-variable CFC or commutative subalgebra transfer |

---

## Ordered Star Algebras

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| `IsSelfAdjoint.of_nonneg`, `LE.le.isSelfAdjoint` | `Algebra/Order/Star/Basic.lean` | 184 |
| `selfAdjoint` (AddSubgroup) | `Algebra/Star/SelfAdjoint.lean` | 338 |
| `selfAdjoint.submodule` (ℝ-submodule) | `Algebra/Star/Module.lean` | 121 |
| `IsSelfAdjoint.add`, `.neg`, `.smul` | `Algebra/Star/SelfAdjoint.lean` | ~120, ~130 |
| `StarRing Rᵐᵒᵖ`, `starRingEquiv` | `Algebra/Star/Basic.lean` | ~281 |
| **`TopologicalRing`** — typeclass for ring with continuous multiplication and negation | `Topology/Algebra/Ring/Basic.lean` | (typeclass definition) |
| **`TopologicalSemiring`** — typeclass for semiring with continuous operations | `Topology/Algebra/Ring/Basic.lean` | (typeclass definition) |
| **`TrivialStar ℝ`** — `star r = r` for all `r : ℝ` instance; used for scalar multiplication under star | `Data/Real/Star.lean` | 21 |

---

## Self-Adjoint Multiplication & Star Properties

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| `IsSelfAdjoint.commute_iff` | `Algebra/Star/SelfAdjoint.lean` | 89–94 |
| `IsSelfAdjoint.mul` (in CommSemigroup) | `Algebra/Star/SelfAdjoint.lean` | 228–231 |
| `IsSelfAdjoint.star_mul_self`, `.mul_star_self` | `Algebra/Star/SelfAdjoint.lean` | 82–87 |
| `IsSelfAdjoint.conjugate`, `.conjugate'`, `.conjugate_self` | `Algebra/Star/SelfAdjoint.lean` | 158–167 |
| `IsSelfAdjoint.mul_self_nonneg` (in StarOrderedRing) | `Algebra/Order/Star/Basic.lean` | 202–204 |

---

## Conjugation & Order Preservation

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`star_left_conjugate_le_conjugate`** | `Algebra/Order/Star/Basic.lean` | 242 |
| **`star_right_conjugate_le_conjugate`** | `Algebra/Order/Star/Basic.lean` | 252 |
| `IsSelfAdjoint.conjugate_le_conjugate` | `Algebra/Order/Star/Basic.lean` | 259 |
| `conjugate_le_conjugate_of_nonneg` | `Algebra/Order/Star/Basic.lean` | 263 |
| `star_left_conjugate_nonneg`, `.star_right_conjugate_nonneg` | `Algebra/Order/Star/Basic.lean` | 211, 227 |
| `IsSelfAdjoint.conjugate_nonneg`, `conjugate_nonneg_of_nonneg` | `Algebra/Order/Star/Basic.lean` | 234, 238 |
| Strict order variants: `star_left_conjugate_lt_conjugate`, `.star_right_conjugate_lt_conjugate` | `Algebra/Order/Star/Basic.lean` | 305, 313 |
| C⋆-algebra norm bounds: `star_left_conjugate_le_norm_smul`, `.star_right_conjugate_le_norm_smul` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` | 449, 463 |

---

## Spectrum / NonnegSpectrumClass

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| `spectrum_nonneg_of_nonneg` | `Algebra/Algebra/Spectrum/Quasispectrum.lean` | 418 |
| `NonnegSpectrumClass` (class definition) | `Algebra/Algebra/Spectrum/Quasispectrum.lean` | 394 |
| **`cfc_mono`** (monotonicity: `∀ x ∈ spectrum ℝ a, f x ≤ g x → cfc f a ≤ cfc g a`) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 920 |
| **`cfc_le_iff`** (CFC ordering iff pointwise ordering on spectrum) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 1031 |
| **`le_algebraMap_iff_spectrum_le`** (element ≤ scalar iff spectrum bounded above) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 1052 |
| **`algebraMap_le_iff_le_spectrum`** (scalar ≤ element iff spectrum bounded below) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` | 1057 |
| **`cfc_tsub`** (tsub with spectrum-dependent bounds) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` | 46 |
| **`mem_Icc_algebraMap_iff_norm_le`** (interval membership via norm) | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` | 246–253 |
| **`spectrum.of_subsingleton`** — `spectrum ℝ a = ∅` for subsingleton algebras (simp) | `Algebra/Algebra/Spectrum/Basic.lean` | 156 |

---

## Convexity

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| `convex_Ici`, `convex_Iic`, `convex_Icc` | `Analysis/Convex/Basic.lean` | 245–254 |
| `ProperCone.convex` | `Analysis/Convex/Cone/Basic.lean` | 92 |
| `ConvexOn`, `ConcaveOn` definitions | `Analysis/Convex/Function.lean` | early |
| **`neg_convexOn_iff`** — `ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f` | `Analysis/Convex/Function.lean` | 783 |
| **`neg_concaveOn_iff`** — `ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f` | `Analysis/Convex/Function.lean` | 796 |
| **`neg_strictConvexOn_iff`**, **`neg_strictConcaveOn_iff`** — negation flips strict convexity/concavity | `Analysis/Convex/Function.lean` | 801, 816 |
| **`ConvexOn.neg`, `ConcaveOn.neg`** — forward-direction aliases (as methods) | `Analysis/Convex/Function.lean` | 819–825 |
| **`ConvexOn.subset`** — restrict `ConvexOn` to a subset with proof of inclusion | `Analysis/Convex/Function.lean` | ~770 |
| **`ConcaveOn.subset`** — restrict `ConcaveOn` to a subset with proof of inclusion | `Analysis/Convex/Function.lean` | ~780 |
| `Convex.sum_mem` (weighted sums in convex sets) | `Analysis/Convex/Combination.lean` | 215–218 |
| `Convex.centerMass_mem` (center of mass stays in convex set) | `Analysis/Convex/Combination.lean` | 191–193 |
| `Convex.finsum_mem` (finsum version of weighted sum) | `Analysis/Convex/Combination.lean` | 224–236 |

---

## Strict Positivity & Convex Cones

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`ConvexCone.strictlyPositive`** (strictly positive cone `{x | 0 < x}`) | `Geometry/Convex/Cone/Basic.lean` | 641–662 |
| **`ConvexCone.smul_mem`** (strictly positive cone closed under positive scalar mult) | `Geometry/Convex/Cone/Basic.lean` | 74–76 |
| **`ConvexCone.add_mem`** (strictly positive cone closed under addition) | `Geometry/Convex/Cone/Basic.lean` | 77–78 |
| `ConvexCone` definition (base) | `Geometry/Convex/Cone/Basic.lean` | 56–63 |
| `smul_pos` (strict inequality under positive scalar multiplication) | `Algebra/Order/Module/Defs.lean` | ~140 |
| `add_pos` (sum of positive elements is positive) | Core library `Order/Basic.lean` | varies |
| `smul_lt_smul_of_pos_left`, `smul_lt_smul_of_pos_right` (positivity-preserving order) | `Algebra/Order/Module/Defs.lean` | 318–423 |

---

## Exponent Identities and Real Powers (rpow in C*-algebras)

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`rpow_add`** — `a ^ (x + y) = a ^ x * a ^ y` (requires `IsUnit a`) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 454–462 |
| **`nnrpow_add`** — `a ^ (x + y) = a ^ x * a ^ y` (for `ℝ≥0` exponents, `0 < x, y`) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 119–124 |
| **`rpow_add_of_nonneg`** — `x ^ (y + z) = x ^ y * x ^ z` (foundation, requires `0 ≤ x, y, z`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 204–205 |
| **`rpow_rpow`** — `(a ^ x) ^ y = a ^ (x * y)` (requires `IsUnit a`, allows negative) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 464–471 |
| **`rpow_rpow_of_exponent_nonneg`** — `(a ^ x) ^ y = a ^ (x * y)` (requires `0 ≤ x, y` only, no `IsUnit`) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 483–488 |
| `nnrpow_nnrpow` | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 157–168 |
| `rpow_mul_rpow_neg`, `rpow_neg_mul_rpow` — `a ^ x * a ^ (-x) = 1` (for `IsUnit a`) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 490–496 |
| `nnrpow_eq_rpow`, `rpow_natCast` (conversions) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 624–625, 444–446 |
| `monotone_nnrpow` (monotonicity for `p ∈ [0,1]`) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean` | 62–86 |
| **`IsStrictlyPositive.rpow`** — `IsStrictlyPositive a → IsStrictlyPositive (a ^ y)` | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` | 732–733 |
| **`continuous_rpow_const`** — `Continuous (·^q)` (requires `0 ≤ q`) | `Analysis/SpecialFunctions/Pow/Continuity.lean` | 228 |
| **`continuousOn_rpow_const`** (NNReal version) — `ContinuousOn (·^r)` on nonneg or excluding zero | `Analysis/SpecialFunctions/Pow/Continuity.lean` | 433–436 |

---

## Classical Real Powers (rpow over ℝ)

**Primary resource:** `Analysis/SpecialFunctions/Pow/Real.lean` — comprehensive classical rpow library

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`rpow_add`** — `x ^ (y + z) = x ^ y * x ^ z` (requires `0 < x`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 204 |
| **`rpow_add_of_nonneg`** — `x ^ (y + z) = x ^ y * x ^ z` (requires `0 ≤ x, y, z`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 218 |
| **`rpow_mul`** — `x ^ (y * z) = (x ^ y) ^ z` (requires `0 ≤ x`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 408 |
| **`rpow_neg`** — `x ^ (-y) = (x ^ y)⁻¹` (requires `0 ≤ x`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 255 |
| **`rpow_zero`** — `x ^ (0 : ℝ) = 1` | `Analysis/SpecialFunctions/Pow/Real.lean` | 120 |
| **`rpow_one`** — `x ^ (1 : ℝ) = x` | `Analysis/SpecialFunctions/Pow/Real.lean` | 148 |
| **`rpow_natCast`** — `x ^ (n : ℝ) = x ^ n` (simp) | `Analysis/SpecialFunctions/Pow/Real.lean` | 62 |
| **`rpow_intCast`** — `x ^ (n : ℝ) = x ^ n` (simp, norm_cast) | `Analysis/SpecialFunctions/Pow/Real.lean` | 57 |
| **`rpow_neg_natCast`** — `x ^ (-n : ℝ) = x ^ (-n : ℤ)` (simp) | `Analysis/SpecialFunctions/Pow/Real.lean` | 65 |
| `rpow_nonneg` (Classical `ℝ` analog) | `Analysis/SpecialFunctions/Pow/Real.lean` | 160 |
| `mul_rpow` — `(x * y) ^ z = x ^ z * y ^ z` (requires `0 ≤ x, 0 ≤ y`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 472 |
| `inv_rpow` — `x⁻¹ ^ y = (x ^ y)⁻¹` (requires `0 ≤ x`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 477 |
| `rpow_rpow_inv` — `(x ^ y) ^ y⁻¹ = x` (requires `0 ≤ x`, `y ≠ 0`, simp) | `Analysis/SpecialFunctions/Pow/Real.lean` | 495 |
| `rpow_inv_rpow` — `(x ^ y⁻¹) ^ y = x` (requires `0 ≤ x`, `y ≠ 0`, simp) | `Analysis/SpecialFunctions/Pow/Real.lean` | 498 |
| `rpow_pos_of_pos` — `0 < x ^ y` (requires `0 < x`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 116 |
| `continuousAt_rpow` — continuity of `(x, y) ↦ x ^ y` | `Analysis/SpecialFunctions/Pow/Continuity.lean` | 215 |
| `continuous_rpow_const` — `Continuous (·^q)` (requires `0 ≤ q`) | `Analysis/SpecialFunctions/Pow/Continuity.lean` | 228 |
| **`rpow_sum_of_pos`** — `a ^ (∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x` (requires `0 < a`) | `Analysis/SpecialFunctions/Pow/Real.lean` | 238 |

**NNReal wrapper:** `Analysis/SpecialFunctions/Pow/NNReal.lean` — analogs for `x : ℝ≥0`

---

## Units and Group Actions

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`IsUnit.smul`** (g • a is a unit when a is) | `Algebra/Group/Action/Units.lean` | 158–161 |
| `Units.smul_def`, `Units.smul_isUnit` | `Algebra/Group/Action/Units.lean` | 35–42 |
| `IsUnit.subInvSMul` (spectrum context) | `Algebra/Algebra/Spectrum/Basic.lean` | 84–88 |

---

## Scalar Multiplication & Powers

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`smul_pow`** — `(r • x) ^ n = r ^ n • x ^ n` (natural numbers) | `Algebra/Group/Action/Defs.lean` | 470 |
| **`smul_zpow`** — `(g • a) ^ n = g ^ n • a ^ n` (integers) | `Algebra/Group/Action/Defs.lean` | 507 |
| **`smul_pow'`** — `@[simp] r • x ^ n = (r • x) ^ n` | `Algebra/Group/Action/Basic.lean` | 188 |
| **`mul_pow`** — `(a * b) ^ n = a ^ n * b ^ n` (commutative monoid) | `Algebra/Group/Basic.lean` | 222 |
| **`zpow_mul`** — `a ^ (m * n) = (a ^ m) ^ n` (integer powers) | `Algebra/Group/Basic.lean` | 471 |
| **`mul_smul_comm`** — `x * s • y = s • (x * y)` (scalar across mult on right) | `Algebra/Group/Action/Defs.lean` | 347 |
| **`smul_mul_assoc`** — `r • x * y = r • (x * y)` (scalar across mult on left) | `Algebra/Group/Action/Defs.lean` | 352 |
| **`smul_mul_smul_comm`** — `(a • b) * (c • d) = (a * c) • (b * d)` (distribute scalars in product) | `Algebra/Group/Action/Defs.lean` | 368 |
| **`mul_smul_mul_comm`** — `(a * b) • (c * d) = (a • c) * (b • d)` (product on both sides) | `Algebra/Group/Action/Defs.lean` | 379 |
| `mul_pow_mul` — `(a * b) ^ n * a = a * (b * a) ^ n` (monoid rearrangement) | `Algebra/Group/Defs.lean` | 656 |

**Typeclasses required for above:**
- `IsScalarTower α β β` — for associative scalar behavior
- `SMulCommClass α β β` — for scalar multiplication to commute
- `MulAction M N` — base action structure

---

## Fin Sums & Vector Notation

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`Fin.sum_univ_two`** — `∑ i : Fin 2, f i = f 0 + f 1` | `Algebra/BigOperators/Fin.lean` | various |
| **`Fin.forall_fin_two`** — `(∀ i : Fin 2, p i) ↔ p 0 ∧ p 1` | `Data/Fin/Basic.lean` | various |
| **`![a₁, a₂]`** vector notation (`vecCons`) | `Data/Fin/VecNotation.lean` | — |
| `Matrix.cons_val_zero` — `![a, ...] 0 = a` (simp) | `Data/Fin/VecNotation.lean` | — |
| `Matrix.cons_val_one` — `![a, b] 1 = b` (simp) | `Data/Fin/VecNotation.lean` | — |
| `Matrix.cons_val_fin_one` — needed for `Fin 2` simp | `Data/Fin/VecNotation.lean` | — |
| `fin_cases` tactic — case-split on `Fin n` | tactic | — |

---

## Matrix Norms & Inner Products (Phase A — HilbertMatrix)

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`Matrix.toMatrixNormedAddCommGroup`** — normed group structure from `M : Matrix n n 𝕜` with `M.PosDef`, inner product `⟪x, y⟫ = Tr(y * M * x†)` | `Analysis/Matrix/Order.lean` | 362–394 |
| **`toMatrixInnerProductSpace`** — `InnerProductSpace` from `M.PosSemidef`, same inner product formula | `Analysis/Matrix/Order.lean` | (follows toMatrixNormedAddCommGroup) |
| **`Matrix.PosDef.one`** — proof that identity matrix `1` satisfies `PosDef` | `LinearAlgebra/Matrix/PosDef.lean` | 204 |
| **`open scoped Matrix.Norms.L2Operator`** — scope activation for L2 operator norm instances on `Matrix n n 𝕜` | `Analysis/CStarAlgebra/Matrix.lean` | 175 |
| **`instL2OpNormedAddCommGroup`, `instL2OpNormedRing`, `instL2OpNormedAlgebra`** — L2 operator norm instances (via scope) | `Analysis/CStarAlgebra/Matrix.lean` | 180–284 |
| **`toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)`** — star algebra equivalence | `Analysis/CStarAlgebra/Matrix.lean` | 102–107 |

---

## Continuous Linear Maps & Operator Algebra

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`CStarAlgebra (E →L[ℂ] E)`** — C⋆-algebra structure on continuous linear maps when E is complete inner product space | `Analysis/CStarAlgebra/ContinuousLinearMap.lean` | — |
| **`StarOrderedRing (E →L[ℂ] E)`** — ordered star-algebra when E is inner product space (adjoint induces order) | `Analysis/InnerProductSpace/StarOrder.lean` | — |
| **`ContinuousLinearMap.adjoint`** — adjoint T† of continuous linear map T, characterized by `⟪T x, y⟫ = ⟪x, T† y⟫` | `Analysis/InnerProductSpace/Adjoint.lean` | — |
| `LinearMap.adjoint` (non-continuous version, for bounded operators on finite-dimensional spaces) | `Analysis/InnerProductSpace/Adjoint.lean` | — |
| **`ContinuousLinearMap.star_eq_adjoint`** — star on CLM equals adjoint when has star structure | `Analysis/InnerProductSpace/Adjoint.lean` | — |
| **`ContinuousLinearMap.IsPositive`** — positive operator: `T.IsSymmetric ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x` | `Analysis/InnerProductSpace/Positive.lean` | 273–274 |
| **`ContinuousLinearMap.reApplyInnerSelf`** — real inner product: `fun x => re ⟪T x, x⟫` | `Analysis/InnerProductSpace/LinearMap.lean` | 270 |
| **`ContinuousLinearMap.reApplyInnerSelf_apply`** — simp lemma: `T.reApplyInnerSelf x = re ⟪T x, x⟫` | `Analysis/InnerProductSpace/LinearMap.lean` | (follows 270) |

---

## Star-Algebra Homomorphisms & Classes

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`StarAlgHom R A B`** — star-algebra homomorphism structure; extends `AlgHom R A B` with `map_star' : φ (star x) = star (φ x)` | `Algebra/Star/StarAlgHom.lean` | 288–291 |
| **Constructor for `StarAlgHom`**: `⟨(f : A →ₐ[R] B), (h : ∀ x, f (star x) = star (f x))⟩` — convenient pattern | `Algebra/Star/StarAlgHom.lean` | (structure definition) |
| **`StarAlgHomClass F R A B`** — typeclass for coercible types that are star-algebra homs; requires `[AlgHomClass F R A B]` and `[StarHomClass F A B]` | `Algebra/Star/StarAlgHom.lean` | (typeclass section) |
| **`AlgHomClass F R A B`** — typeclass: `F` is coercible to an algebra homomorphism `A →ₐ[R] B` | `Algebra/Hom/Equiv.lean` | (typeclass definition) |
| **`StarHomClass F A B`** — typeclass: `F` coerces to a function `A → B` that preserves star: `φ (star x) = star (φ x)` | `Algebra/Star/Hom.lean` | (typeclass definition) |
| **`StarModule ℂ H`** — module structure respecting star: `star (c • x) = conj c • star x` | `Algebra/Star/Module.lean` | (typeclass definition) |
| **`star_smul_of_star`** — `star (c • x) = conj c • star x` lemma for `StarModule` | `Algebra/Star/Module.lean` | (lemma) |
| **`IsSelfAdjoint.map`** — star homomorphisms preserve self-adjointness: `IsSelfAdjoint x → [StarHomClass F A B] → IsSelfAdjoint (f x)` | `Algebra/Star/SelfAdjoint.lean` | 98 |
| **`IsSelfAdjoint.map_spectrum_real`** — injective star-alg hom preserves real spectrum for self-adjoint elements | `Analysis/CStarAlgebra/Hom.lean` | 24–27 |

---

## Linear Maps / Algebra Homomorphisms

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| `Algebra.lmul : A →ₐ[R] End R A` | `Algebra/Algebra/Bilinear.lean` | 137 |
| `pow_mulLeft`, `pow_mulRight` | `Algebra/Algebra/Bilinear.lean` | 111–114 |
| `NonUnitalAlgHom.Lmul` (continuous) | `Analysis/Normed/Operator/Mul.lean` | 65 |
| **`StarAlgHom`** — star-algebra homomorphism (subtype of `RingHom` preserving star) | `Algebra/Star/Hom.lean` | — |

---

## MulOpposite Algebra Infrastructure

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`MulOpposite.instNonUnitalNormedRing`** — `NonUnitalNormedRing αᵐᵒᵖ` instance | `Analysis/Normed/Ring/Basic.lean` | 497 |
| **`MulOpposite.instNormedRing`** — `NormedRing αᵐᵒᵖ` instance | `Analysis/Normed/Ring/Basic.lean` | 521 |
| **`MulOpposite.instNormedAlgebra`** — `NormedAlgebra 𝕜 Eᵐᵒᵖ` instance | `Analysis/Normed/Module/Basic.lean` | 387 |
| **`MulOpposite.CStarRing`** — `CStarRing Eᵐᵒᵖ` instance using `norm_self_mul_star` | `Analysis/CStarAlgebra/Basic.lean` | 199–202 |
| **`StarRing Rᵐᵒᵖ`** — `star(op a) = op(star a)` structure | `Algebra/Star/Basic.lean` | 545 |
| **`starRingEquiv : R ≃+* Rᵐᵒᵖ`** — ring iso via `x ↦ op(star x)` | `Algebra/Star/Basic.lean` | 283 |
| **`op_star : op (star r) = star (op r)`** — simp lemma, conjugation commutes with opposite | `Algebra/Star/Basic.lean` | 533 |
| **`StarModule R Mᵐᵒᵖ`** — `StarModule` instance for opposite: `star(r • m) = star r • star m` | `Algebra/Star/Basic.lean` | 548 |
| **`StarAlgEquiv R A B`** — star algebra equivalence, extends `StarRingEquiv` with `map_smul'` | `Algebra/Star/StarAlgHom.lean` | 627–630 |
| **`MulOpposite.instAlgebra`** — `Algebra R Aᵐᵒᵖ` via `toOpposite` | `Algebra/Algebra/Opposite.lean` | 44 |
| **`MulOpposite.algebraMap_apply : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c)`** — simp lemma | `Algebra/Algebra/Opposite.lean` | 53 |
| **`AlgEquiv.op`** — converts `A ≃ₐ[R] B` to `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ` | `Algebra/Algebra/Opposite.lean` | 141 |
| **`AlgEquiv.opComm`** — converts `A ≃ₐ[R] Bᵐᵒᵖ` to `Aᵐᵒᵖ ≃ₐ[R] B` | `Algebra/Algebra/Opposite.lean` | 169 |
| **`AlgEquiv.opOp`** — isomorphism `A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ` (double opposite) | `Algebra/Algebra/Opposite.lean` | 63 |

---

## MulOpposite Order Infrastructure

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`PartialOrder αᵐᵒᵖ`** — lifted order via `unop`, preserves ordering: `op a ≤ op b ↔ a ≤ b` | `Algebra/Order/Group/Opposite.lean` | 33 |
| **`op_nonneg : 0 ≤ op a ↔ 0 ≤ a`** — simp lemma, nonnegativity preserved under opposite | `Algebra/Order/Group/Opposite.lean` | 57 |
| **`unop_nonneg : 0 ≤ unop a ↔ 0 ≤ a`** — converse direction | `Algebra/Order/Group/Opposite.lean` | 55 |
| **`IsOrderedRing Rᵐᵒᵖ`** — ordered ring for opposite, swaps left/right multiplication order properties | `Algebra/Order/Ring/Opposite.lean` | 24–27 |
| **`StarOrderedRing Rᵐᵒᵖ`** — star-ordered ring for opposite, preserves star structure via `le_iff` | `Algebra/Order/Star/Basic.lean` | 382–390 |

---

## Continuous Linear Maps & Operator Topology

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`continuous_op : Continuous (MulOpposite.op : A → Aᵐᵒᵖ)`** — opposite operation is continuous | `Topology/Algebra/Algebra.lean` or `Topology/Order/DenselyOrdered.lean` | (in Topology section) |
| **`continuous_unop : Continuous (MulOpposite.unop : Aᵐᵒᵖ → A)`** — unop is continuous | (same) | (in Topology section) |

---

## Conjugation & Unitary Actions

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`ConjAct`** — conjugation action typeclass on rings | `Algebra/Ring/Action/ConjAct.lean` | — |
| **`Unitary.spectrum_subset_circle`** — spectrum of unitary element ⊆ unit circle | `Analysis/CStarAlgebra/Spectrum.lean` | 75 |
| **`cfc_unitary_iff`** — CFC of `f` for unitary element via restricted spectrum | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unitary.lean` | 29 |
| **`IsometricContinuousFunctionalCalculus`** — typeclass for isometric CFC behavior | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean` | 31 |
| **`isometry_cfcHom`** — CFC homomorphism is an isometry `‖cfc f a‖ ≤ ‖f‖_* ‖a‖` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean` | 45 |
| **`SpectrumRestricts.isometric_cfc`** — builds isometric CFC via spectrum restriction | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean` | 150–200 |

---

## Induction Principles & Closure

| Declaration / Topic | File | Line (approx) |
|---------------------|------|---------------|
| **`AddSubmonoid.closure_induction`** — induction on closure membership: `closure_induction mem zero add ha` proves `motive x hx` for all `x ∈ closure s` | `Algebra/Group/Submonoid/Basic.lean` | 162–170 |
| Usage pattern (Lean 4): `induction ha using AddSubmonoid.closure_induction with \| mem b hb => ... \| zero => ... \| add b c _ _ ihb ihc => ...` | (tactic) | — |
| **`Submonoid.closure_induction`** — multiplicative version of closure induction | `Algebra/Group/Submonoid/Basic.lean` | (adjacent to 162) |
