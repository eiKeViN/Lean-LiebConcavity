---
description: Search Mathlib for lemmas/instances about a concept
argument-hint: [concept or math description]
allowed-tools: Glob, Grep, Read, Bash, Agent, Write, Edit
model: sonnet
---

Search for Mathlib lemmas/definitions/instances related to: **$ARGUMENTS**

## Step 1 — Check the pre-cached notes

Read `memory/mathlib_key_paths.md` from the project memory at
`C:\Users\eiKevinZ\.claude\projects\c--Users-eiKevinZ-my-coursework-Lean-LiebConcavity\memory\mathlib_key_paths.md`.

If a relevant result is found, report it immediately with the file:line reference and stop.

## Step 2 — LeanSearch (primary: fast semantic search)

Query the LeanSearch API. This is a **semantic search engine** over Mathlib — use natural
language or math phrases, NOT exact Lean identifier names.

```bash
curl -s "https://leansearch.net/search" \
  -X POST \
  -H "Content-Type: application/json" \
  -d '{"query":["$ARGUMENTS"],"num_results":8}'
```

Parse the JSON response. Each result has:
- `result.name` — array of name segments, e.g. `["Matrix","isStrictlyPositive_iff_posDef"]`
- `result.module_name` — array of path segments, e.g. `["Mathlib","Analysis","Matrix","Order"]`
- `result.signature` — the theorem/def signature string
- `result.type` — full elaborated type
- `result.kind` — `"theorem"`, `"def"`, `"instance"`, etc.
- `result.informal_description` — natural language description
- `distance` — similarity score (lower = more relevant; anything below ~0.35 is a strong match)

**If LeanSearch returns strong matches (distance < 0.35)**: report them and proceed to Step 3.

**If LeanSearch returns weak or no matches**: fall through to Step 2b.

## Step 2b — Local Mathlib grep (fallback)

Only if Step 2 failed or returned weak results. Launch an Explore agent:

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

## Step 3 — Verify and enrich

For each LeanSearch result, derive the file path as:
```
.lake/packages/mathlib/Mathlib/<module_name joined by "/">.lean
```
e.g. `["Mathlib","Analysis","Matrix","Order"]` → `Analysis/Matrix/Order.lean`

If you need the exact line number or surrounding proof context, grep or read the file.

## Step 4 — Format results

Present results as:

| Declaration | File:Line | Type signature (abbreviated) |
|-------------|-----------|-------------------------------|
| ...         | ...       | ...                           |

If multiple declarations are found, group by topic. For LeanSearch results, include the
`informal_description` if it adds clarity.

## Step 5 — Update memory (if new paths discovered)

For any newly found file paths **not already listed** in `mathlib_key_paths.md`,
append them to the appropriate section. Add a new section if the topic is not covered yet.
