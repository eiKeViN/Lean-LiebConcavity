---
description: Search Mathlib for lemmas/instances about a concept
argument-hint: [concept or math description]
allowed-tools: Glob, Grep, Read, Agent, Write, Edit
model: haiku
---

Search for Mathlib lemmas/definitions/instances related to: **$ARGUMENTS**

## Step 1 — Check the pre-cached notes

Read the following files and check if the concept is already covered:
- `notes/01_ordered_cstar_basics.md`
- `notes/02_cfc_star_hom.md`

If a relevant result is found, report it immediately with the file:line reference and stop.

## Step 2 — Mathlib search (if not in notes)

Launch an Explore agent with the following task:

> Search the Mathlib source tree at `.lake/packages/mathlib/Mathlib/` for declarations
> related to: **$ARGUMENTS**
>
> Priority search directories (check these first):
> - `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/`
> - `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/`
> - `Algebra/Order/Star/`
> - `Algebra/Star/`
> - `Analysis/Convex/`
> - `Algebra/Algebra/`
> - `Algebra/Module/LinearMap/`
>
> Search strategy (run all three in parallel):
> 1. **Name search**: grep for declaration names matching the concept
> 2. **Keyword search**: grep docstrings and comments for the concept keywords
> 3. **Typeclass search**: grep for relevant typeclass names the concept might require
>
> For each match, report: declaration name, file path (relative to Mathlib/), line number,
> and 3–5 lines of context showing the type signature.

## Step 3 — Format results

Present results as:

| Declaration | File:Line | Type signature (abbreviated) |
|-------------|-----------|-------------------------------|
| ...         | ...       | ...                           |

If multiple declarations are found, group by topic.

## Step 4 — Update memory (if new paths discovered)

Read `memory/mathlib_key_paths.md` from the project memory at
`C:\Users\eiKevinZ\.claude\projects\c--Users-eiKevinZ-my-coursework-Lean-LiebConcavity\memory\mathlib_key_paths.md`.

If any newly found file paths are **not already listed** in that file, append them
to the appropriate section. Add a new section if the topic is not covered yet.
