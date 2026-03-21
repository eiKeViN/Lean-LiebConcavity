---
description: Produce a Lean 4 sorry-stub for a blueprint declaration
argument-hint: [blueprint-label] [informal math description]
allowed-tools: Read, Grep, Write, Edit
model: opus
---

Produce a correct Lean 4 sorry-stub for the following blueprint declaration:

**Input:** $ARGUMENTS
(Format: `[blueprint-label] informal mathematical description`)

## Context to load first

Read the following files before generating the stub:

1. `CLAUDE.local.md` — for the Blueprint Correspondence table and Coding Conventions
2. `notes/01_ordered_cstar_basics.md` — for the standard typeclass stack and key lemmas
3. The relevant source file in `LeanLiebConcavity/` if it already exists (check `Jensen.lean`, `Defs.lean`, `Lowner.lean`, `Perspective.lean`, `Main.lean`)

## Output format

Produce a self-contained Lean 4 code block with:

### 1. Imports
Use the minimal import set. Standard baseline:
```lean
import LeanLiebConcavity.ForMathlib
import LeanLiebConcavity.Defs
-- add further imports only if required (e.g. Rpow/Basic for rpow)
```

### 2. Variable block (if not already in the file)
```lean
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
```
Adjust if the declaration is a `def` (no variable block needed) or if extra
typeclasses are required (e.g. `[NonnegSpectrumClass ℝ A]`).

### 3. The declaration itself
Follow these conventions from CLAUDE.local.md:
- Implicit set parameters: `{I : Set ℝ}`
- Hypotheses as named arguments: `(hI : Convex ℝ I)`
- Self-adjoint hypotheses: `(ha : IsSelfAdjoint a)` — or omit if `0 ≤ a` is given (implies SA)
- Spectrum hypotheses: `(ha_spec : spectrum ℝ a ⊆ I)`
- Blueprint comment on the line before the declaration:
  `-- [blueprint-label] Author Year, short description`
- End with `:= by\n  sorry`

### 4. Uncertainty note
If the correct imports or typeclasses are unclear, append a comment block:
```lean
-- TODO: verify imports — consider running /mathlib-search "[concept]"
```

## Example output shape

```lean
import LeanLiebConcavity.Defs

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- [thm:example] Author Year, brief statement
theorem ExampleTheorem
    {I : Set ℝ} (hI : Convex ℝ I)
    {f : ℝ → ℝ} (hf : ContinuousOn f I)
    {a : A} (ha : IsSelfAdjoint a) (ha_spec : spectrum ℝ a ⊆ I) :
    0 ≤ cfc f a := by
  sorry

end CFC
```

Do NOT attempt to fill in the proof. The sorry is intentional.
