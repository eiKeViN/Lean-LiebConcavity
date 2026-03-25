# CLAUDE.local.For md — Lieb Concavity Formalization Project

## Project Overview

This is a **Lean 4** formalization project proving **Lieb's concavity theorem** and
related results (Lieb's extension theorem, Ando's convexity theorem), following the
proof strategy of:

- **[Nik2013]** Nikoufar–Ebadian–Eshaghi Gordji, *Adv. Math.* 248 (2013) 531–533
- **[Eba2011]** Ebadian–Nikoufar–Eshaghi Gordji, *PNAS* 108 (2011) 7313–7314
- **[HP2003]** Hansen–Pedersen, *B. London Math. Soc.* 35 (2003) 553–564
- **[HP1982]** Hansen–Pedersen, *Math. Ann.* 258 (1982) 229–241

<!-- BLUEPRINT TRACKING TEMPORARILY DISABLED: do not enforce blueprint correspondence
during active formalization. The blueprint will be generated/updated once most
declarations are formalized. See ## Blueprint Correspondence below for the mapping.

The project is structured around a **Lean Blueprint** (`lieb_blueprint.tex`) which is
the source of truth for the dependency graph. Every Lean declaration should correspond
to a labelled node in the blueprint. The blueprint architecture and plugin used in this project is **leanblueprint** (`https://github.com/PatrickMassot/leanblueprint?tab=readme-ov-file`).
-->

---

## Dependencies

- **Mathlib** (latest pinned version — see `lean-toolchain`)

### Critical rules about dependencies
- **Do not modify any files inside the `Mathlib` source tree.**
- If something is missing from Mathlib and needs to be added, define it in
  `LeanLiebConcavity/ForMathlib.lean` with a comment marking it as a potential upstream
  contribution.

---

## Repository Structure

```
Lean-LiebConcavity/
├── CLAUDE.local.md            ← this file
├── lakefile.lean              ← project + dependency declarations
├── lean-toolchain             ← pinned Lean version
├── lieb_blueprint.tex         ← LaTeX blueprint (disabled during active formalization)
├── LeanLiebConcavity.lean     ← top-level import file
└── LeanLiebConcavity/
    ├── Basic.lean             ← basic shared lemmas and imports
    ├── ForMathlib.lean        ← lemmas not yet in Mathlib
    ├── Defs.lean              ← core definitions (MatrixConvex, PerspectiveFunction,
    │                             GenPerspectiveFunction, OperatorPowerMean)
    ├── HStarAlgebra.lean      ← H*-algebra typeclass (Ambrose 1945); Lmul/Rmul as
    │                             StarAlgHom; CFC commutativity L_{f(a)} = f(L_a)
    ├── Jensen.lean            ← Jensen's operator inequality (HP1982, HP2003)
    └── Main.lean              ← Lieb, Lieb extension, Ando, Corollary 1.3
```

---

## Blueprint Correspondence

<!-- TEMPORARILY DISABLED: do not require \lean{} tags or update lieb_blueprint.tex
during active formalization. Revisit when most declarations are complete. -->

The correspondence (for future reference) is:

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
- Do not add `import`s from `Lean-QuantumInfo` that pull in the entire library;
  import only the specific files needed.

---

## Notes for Proof Development

- **Jensen nodes are hardest:** `JensenOperator1982` and `JensenOperator2003` should
  be attempted last or taken as axioms initially.
- **Check Lean-QuantumInfo's `Lieb.lean`** before working on `Main.lean` — understand
  what they have sorry'd and ensure no duplication.

---

## Lean Patterns Quick Reference

### Minimal typeclass stack for ordered CFC

```lean
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
```

`CStarAlgebra A` subsumes `Ring`, `StarRing`, `TopologicalSpace`, `NormedAlgebra ℂ A`,
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint`, and `T2Space`. The two extra instances
add the partial order and cone axiom. This is the pattern from `ExpLog/Order.lean`.

### Key Mathlib paths

Maintained in memory at:
`C:\Users\eiKevinZ\.claude\projects\c--Users-eiKevinZ-my-coursework-Lean-LiebConcavity\memory\mathlib_key_paths.md`

Updated automatically by `/mathlib-search`. Check there for verified lemma names,
file paths, and line numbers before using any Mathlib declaration.

### Standard import block for CFC work

```lean
import LeanLiebConcavity.Defs
-- Defs transitively imports:
--   Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
--   Mathlib.Analysis.Convex.Function
-- For rpow (a ^ y for y : ℝ), add:
--   import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
-- For StarAlgHom.map_cfc, add:
--   import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
```

### Slash commands available in this project

- `/mathlib-search [concept]` — structured Mathlib search, updates memory with new paths
- `/formalize [blueprint-label] [informal description]` — produces a correct Lean stub

### Planning workflow

When making a plan that depends on specific Mathlib lemmas, typeclass instances, or
definitions, run `/mathlib-search` to verify names before finalizing the plan. Never
use guessed or unverified Mathlib names in a plan.
