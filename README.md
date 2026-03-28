# Lean-LiebConcavity


A **Lean 4 / Mathlib** formalization of **Lieb's concavity theorem**, a key theorem in Quantum Information, and related results provable by same approach including Lieb's extension theorem and Ando's convexity theorem. The present approach enables the generalization within an abstract H\*-algebra framework (Ambrose 1945). Key foundations for the approach include: Jensen's operator inequality (*sorried*), Löwner's theorem (*sorried*), and the H\*-algebra framework with cfc on left/right multiplication operators (*in progress*).

Main references:

- M. Nikoufar, A. Ebadian, M. Eshaghi Gordji, *Adv. Math.* **248** (2013) 531–533
- A. Ebadian, M. Nikoufar, M. Eshaghi Gordji, *PNAS* **108** (2011) 7313–7314
- F. Hansen, G. K. Pedersen, *Bull. London Math. Soc.* **35** (2003) 553–564
- F. Hansen, G. K. Pedersen, *Math. Ann.* **258** (1982) 229–241
- Y. Li, D. Wu, *J. Operator Theory* **67** (2012) 329–337

## Structure

| File | Contents |
|------|----------|
| `Defs.lean` | Core definitions: `MatrixConvex`, `PerspectiveFunction`, `GenPerspectiveFunction`, `OperatorPowerMean` |
| `HStarAlgebra.lean` | H\*-algebra typeclass; `Lmul`/`Rmul` as star-algebra homs (*done*); CFC commutativity (*done for Lmul; Rmul in progress*)|
| `Jensen.lean` | Jensen's operator inequality (*done, sorried*) |
| `Main.lean` | Concavity/convexity of General Perspective Function (*done*), Lieb concavity + Lieb extension + Ando convexity (*todo*) |
| `ForMathlib.lean` | "Missing lemmas" in Mathlib (*updating*) |

## Building

Requires a compatible Lean 4 toolchain (see `lean-toolchain`).

```bash
lake build
