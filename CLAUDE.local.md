# CLAUDE.local.For md — Lieb Concavity Formalization Project

## Project Overview

This is a **Lean 4** formalization project proving **Lieb's concavity theorem** and
related results (Lieb's extension theorem, Ando's convexity theorem), following the
proof strategy of:

- **[Nik2013]** Nikoufar–Ebadian–Eshaghi Gordji, *Adv. Math.* 248 (2013) 531–533
- **[Eba2011]** Ebadian–Nikoufar–Eshaghi Gordji, *PNAS* 108 (2011) 7313–7314
- **[HP2003]** Hansen–Pedersen, *B. London Math. Soc.* 35 (2003) 553–564
- **[HP1982]** Hansen–Pedersen, *Math. Ann.* 258 (1982) 229–241

The project is structured around a **Lean Blueprint** (`lieb_blueprint.tex`) which is
the source of truth for the dependency graph. Every Lean declaration should correspond
to a labelled node in the blueprint. The blueprint architecture and plugin used in this project is **leanblueprint** (`https://github.com/PatrickMassot/leanblueprint?tab=readme-ov-file`).

---

## Dependencies

- **Mathlib** (latest pinned version — see `lean-toolchain`)
- **Lean-QuantumInfo** (`https://github.com/Timeroot/Lean-QuantumInfo`) — provides
  trace inner product, matrix positivity infrastructure, and quantum information
  primitives. Pinned to a specific commit in `lake-manifest.json`.

### Critical rules about dependencies
- **Do not modify any files inside the `Lean-QuantumInfo` or `Mathlib` source trees.**
- If something is already defined in `Lean-QuantumInfo` (e.g. trace inner product,
  `MState`), **reuse it via import** rather than redefining it.
- If something is missing from both dependencies and needs to be added, define it in
  `LiebConcavity/ForMathlib.lean` with a comment marking it as a potential upstream
  contribution.

---

## Repository Structure

```
LiebConcavity/
├── CLAUDE.md                  ← this file
├── lakefile.lean              ← project + dependency declarations
├── lean-toolchain             ← pinned Lean version
├── lieb_blueprint.tex         ← LaTeX blueprint (source of truth)
├── LiebConcavity.lean         ← top-level import file
└── LiebConcavity/
    ├── ForMathlib.lean        ← lemmas not yet in Mathlib or Lean-QuantumInfo
    ├── Defs.lean              ← core definitions (MatrixConvex, PerspectiveFunction,
    │                             GenPerspectiveFunction, OperatorPowerMean)
    ├── Jensen.lean            ← Jensen's operator inequality (HP1982, HP2003)
    ├── Lowner.lean            ← Löwner's theorem + power function convexity/concavity
    ├── Perspective.lean       ← Ebadian et al. perspective function results
    ├── PowerMean.lean         ← Operator (α,β)-power mean concavity/convexity
    └── Main.lean              ← Lieb, Lieb extension, Ando, Corollary 1.3
```

---

## Blueprint Correspondence

Every declaration must have a matching `\lean{}` tag in `lieb_blueprint.tex`.
The correspondence is:

| Blueprint label                        | Lean declaration                          |
|----------------------------------------|-------------------------------------------|
| `def:matrix_convex`                    | `MatrixConvex`                            |
| `def:perspective`                      | `PerspectiveFunction`                     |
| `def:gen_perspective`                  | `GenPerspectiveFunction`                  |
| `def:power_mean`                       | `OperatorPowerMean`                       |
| `def:trace_inner_product`              | (reuse from `Lean-QuantumInfo`)           |
| `thm:jensen_1982`                      | `JensenOperator1982`                      |
| `thm:jensen_2003`                      | `JensenOperator2003`                      |
| `thm:lowner`                           | `LownerTheorem`                           |
| `cor:power_fn_concave`                 | `PowerFnMatrixConcave`                    |
| `cor:power_fn_convex`                  | `PowerFnMatrixConvex`                     |
| `thm:perspective_iff_matrix_convex`    | `PerspectiveIffMatrixConvex`              |
| `cor:perspective_iff_matrix_concave`   | `PerspectiveIffMatrixConcave`             |
| `thm:gen_perspective_jointly_convex`   | `GenPerspectiveJointlyConvex`             |
| `cor:gen_perspective_jointly_concave`  | `GenPerspectiveJointlyConcave`            |
| `thm:power_mean_jointly_concave`       | `PowerMeanJointlyConcave`                 |
| `thm:power_mean_jointly_convex`        | `PowerMeanJointlyConvex`                  |
| `lem:trace_identity`                   | `TraceIdentity`                           |
| `thm:lieb`                             | `LiebConcavity`                           |
| `thm:lieb_extension`                   | `LiebExtension`                           |
| `cor:jointly_convex_trace`             | `JointlyConvexTrace`                      |
| `thm:ando_convexity`                   | `AndoConvexity`                           |

---

## Coding Conventions

### Sorries
- All declarations start as `sorry`-stubs — this is expected and intentional.
- Mark every sorry with a comment indicating which blueprint node it belongs to and
  what the mathematical content is. Example:
  ```lean
  -- [thm:jensen_1982] Hansen–Pedersen 1982, Thm 2.1
  theorem JensenOperator1982 ... := by
    sorry
  ```
- **Do not remove a sorry unless the proof is complete and `lake build` passes.**

### Style
- Use `variable` blocks at the top of each file for shared assumptions
  (e.g. `variable {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)`).
- Prefer `PosDef` and `PosSemidef` from Mathlib over ad hoc positivity assumptions.
- All matrix types are over `ℂ` (complex numbers) unless stated otherwise.
- Index types are `Fin n` for explicit finite dimension.

### What NOT to do
- Do not write proofs for `JensenOperator1982` or `JensenOperator2003` from scratch —
  these are the hardest nodes and will be handled manually.
- Do not rename existing declarations once the blueprint `\lean{}` tags are set.
- Do not add `import`s from `Lean-QuantumInfo` that pull in the entire library;
  import only the specific files needed.

---

## Scaffolding Task (initial Claude Code brief)

When setting up the project for the first time, the goal is:

1. Create `lakefile.lean` with Mathlib + Lean-QuantumInfo dependencies.
2. Create `lean-toolchain` matching Lean-QuantumInfo's pinned version.
3. Create all `.lean` files in the structure above.
4. Populate each file with `sorry`-stubbed declarations matching the blueprint table,
   with correct type signatures where feasible.
5. Ensure `lake build` succeeds (all sorries, no import errors).

Do **not** attempt to fill in any proofs during scaffolding.

---

## Notes for Future Proof Development

- **Start at the leaves:** `PowerFnMatrixConcave` and `PowerFnMatrixConvex` are the
  best entry points — they may be close to existing Mathlib lemmas in
  `Analysis.SpecialFunctions.Pow`.
- **Jensen nodes are hardest:** `JensenOperator1982` and `JensenOperator2003` should
  be attempted last or taken as axioms initially.
- **Check Lean-QuantumInfo's `Lieb.lean`** before working on `Main.lean` — understand
  what they have sorry'd and ensure no duplication.
- When a proof is complete, update `lieb_blueprint.tex` by adding `\leanok` to the
  corresponding environment.

---

## Lean Patterns Quick Reference

### Minimal typeclass stack for ordered CFC

```lean
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
```

`CStarAlgebra A` subsumes `Ring`, `StarRing`, `TopologicalSpace`, `NormedAlgebra ℂ A`,
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint`, and `T2Space`. The two extra instances
add the partial order and cone axiom. This is the pattern from `ExpLog/Order.lean`.

### Key Mathlib paths (relative to `.lake/packages/mathlib/Mathlib/`)

| Topic | Path |
|-------|------|
| CFC unital | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` |
| CFC order | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` |
| CFC uniqueness / `StarAlgHom.map_cfc` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean` |
| rpow (`a ^ y` for `y : ℝ`) | `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean` |
| Ordered star rings | `Algebra/Order/Star/Basic.lean` |
| Self-adjoint submodule | `Algebra/Star/Module.lean` |
| `Algebra.lmul`, `pow_mulLeft` | `Algebra/Algebra/Bilinear.lean` |
| Convexity basics | `Analysis/Convex/Basic.lean` |
| `NonnegSpectrumClass` instance | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean` |

### Standard import block for CFC work

```lean
import LeanLiebConcavity.Defs
-- Defs transitively imports:
--   Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
--   Mathlib.Analysis.Convex.Function
-- For rpow (a ^ y for y : ℝ), add:
--   import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
```

### Key facts (see `notes/01_ordered_cstar_basics.md` for full details)

- `0 ≤ a → IsSelfAdjoint a`: `IsSelfAdjoint.of_nonneg ha` (or `ha.isSelfAdjoint`)
- `0 ≤ a → spectrum ℝ a ⊆ [0,∞)`: `spectrum_nonneg_of_nonneg ha hx` (via `NonnegSpectrumClass`)
- `0 ≤ cfc f a` when `f ≥ 0` on spectrum: `cfc_nonneg (fun x hx => ...)`
- `0 ≤ a ^ y` for any `y : ℝ` (even negative): `rpow_nonneg` (`@[simp]`)
- Positive cone is convex: `convex_Ici 0`
- Self-adjoint elements form ℝ-subspace: `selfAdjoint.submodule ℝ A`

### Slash commands available in this project

- `/mathlib-search [concept]` — structured Mathlib search, updates memory with new paths
- `/formalize [blueprint-label] [informal description]` — produces a correct Lean stub
