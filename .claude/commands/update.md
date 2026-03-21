---
description: Update mathlib_key_paths.md and notes with newly discovered Mathlib results
argument-hint: [description of new results or topic area, e.g. "Fin sums and vector notation lemmas used today"]
allowed-tools: Glob, Grep, Read, Agent, Write, Edit
model: haiku
---

Update the project's Mathlib reference files with newly discovered results related to: **$ARGUMENTS**

## Step 1 — Gather what's new

Read the current conversation context to identify Mathlib declarations, file paths, and lemmas that were discovered or used. Focus on:
- Declaration names (e.g. `Fin.sum_univ_two`, `rpow_add`)
- File paths relative to `.lake/packages/mathlib/Mathlib/`
- Approximate line numbers
- Brief description of what each declaration does

If the argument is vague (e.g. "results used today"), scan recent tool calls and code changes in the conversation for Mathlib references.

## Step 2 — Update `mathlib_key_paths.md`

Read the current memory file:
`C:\Users\eiKevinZ\.claude\projects\c--Users-eiKevinZ-my-coursework-Lean-LiebConcavity\memory\mathlib_key_paths.md`

For each new result:
1. Check if it's **already listed** — if so, skip it
2. Find the **appropriate section** (CFC, Ordered Star Algebras, Convexity, etc.)
3. If no section fits, **create a new section** with a descriptive heading
4. Add entries in the existing table format:
   ```
   | **`declaration_name`** — brief description | `Relative/Path/To/File.lean` | line_number |
   ```

Use `Edit` to append entries to the correct section. Do not rewrite the entire file.

## Step 3 — Update or create notes

Check if the new results fit into an existing note file:
- `notes/01_ordered_cstar_basics.md` — typeclass stack, positivity, spectrum, CFC basics
- `notes/02_cfc_star_hom.md` — CFC under star-algebra homomorphisms

If the results belong to an existing note:
- Use `Edit` to add a new subsection with the relevant declarations, their signatures, and usage notes

If the results represent a **new topic** not covered by existing notes:
- Create a new note file `notes/NN_topic_name.md` (where NN is the next number)
- Include: mathematical context, key declarations with signatures, usage patterns, and gotchas

**Only create a new note if there are 3+ related declarations worth documenting.** For 1-2 isolated results, just updating `mathlib_key_paths.md` is sufficient.

## Step 4 — Verify line numbers (optional)

If you have access to the Mathlib source tree, spot-check 2-3 line numbers by grepping:
```
Grep for the declaration name in the listed file path
```
Update any stale line numbers found.

## Step 5 — Report

Summarize what was added/updated:
- Number of new entries in `mathlib_key_paths.md`
- Any new note files created
- Any existing notes updated
- Any stale entries corrected
