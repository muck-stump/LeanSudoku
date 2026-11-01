# TODO — Lean 4 port status

Handoff notes for continuing this port. Branch: `lean4-current-setup` (based on `main`).
Verified environment: Lean `v4.35.0`, Mathlib tag `v4.35.0`, Lake (bundled), elan ≥ 2.0.

Reproduce the current state from a fresh clone:

```sh
lake exe cache get && lake build          # ✅ exit 0 (library = LeanSudoku/Basic.lean)
lake env lean LeanSudoku/STactic.lean     # ❌ known-failing file, errors listed below
```

## Done on this branch

- [x] `lean-toolchain`: `v4.13.0-rc3` → `v4.35.0` (current stable). The old toolchain
      was not merely stale: binaries built by it abort on current macOS
      (`dyld: __DATA_CONST segment missing SG_READ_ONLY flag`, exit 134 — hit when
      running mathlib's `cache` executable), so the old pin was unusable here.
- [x] `lakefile.toml`: Mathlib pinned to `rev = "v4.35.0"` (stable tag matching the
      toolchain) instead of floating on `master`. Mathlib tags correspond 1:1 to Lean
      releases — keep `lean-toolchain` and this `rev` in lockstep.
- [x] `lake-manifest.json` regenerated via `lake update mathlib`; every transitive dep
      now resolved from Mathlib v4.35.0's own manifest (incl. new dep `plausible`).
- [x] `LeanSudoku/Basic.lean` ported to current Mathlib (needed three changes):
  - `open Set Fin.NatCast` — the key discovery: Lean core provides the
    `NatCast (Fin n)` instance **scoped** under `Fin.NatCast` ("activated locally via
    `open Fin.NatCast`", see `Init/Data/Fin/Lemmas.lean`). That is what makes the
    Lean-3-style coordinates `(3 * i.1 : ℕ)` in `box_cases`/`box_conflict` elaborate at
    type `Fin 9`/`Fin 3`; the existing proofs (`rw [Fin.val_cast_of_lt]`) were already
    written against that coercion.
  - `structure Sudoku :=` → `structure Sudoku where` (deprecated syntax).
  - `push_neg` → `push Not` (deprecated in current Mathlib).
- [x] README rewritten with reproducible build/setup instructions.
- [x] This file.

Remaining build output is two informational warnings per module
("`imports Mathlib.…` … consider adding `module`") — harmless; adopting the module
system downstream is out of scope.

## Next steps (priority order)

### 1. Finish `LeanSudoku/STactic.lean` and put it in the build

The file is **not** imported by `LeanSudoku.lean`, so `lake build` ignores it today.
Check with `lake env lean LeanSudoku/STactic.lean`. Known errors at v4.35.0:

- [ ] **L71 `evalFin`** — `return some ((n : Fin 9), proof)`: `n : ℕ` has no coercion to
      `Fin 9`. Fix: `open Fin.NatCast` (same as `Basic.lean`) or use `Fin.ofNat 9 n`.
      Also re-check `Mathlib.Meta.NormNum.deriveNat` (now at
      `Mathlib/Tactic/NormNum/Core.lean:120`) — its returned proof must state
      `e = (n : Fin 9)` for `evalFin`'s callers to typecheck.
- [ ] **L135/L137 `Fin.ne_of_mod_ne`** — `i = ↑n`, `j = ↑m` hit the same missing ℕ→Fin
      coercion (error at 135:14 and 135:28); after that the closing `simpa [hi, hj]`
      fails (137:2). Redo the proof, e.g. `Fin.ne_of_val_ne` + `simp`/`omega` on
      `Fin.val` with `n % 9 ≠ m % 9`.
- [ ] **L142 `showByNormNum`** — `Mathlib.Meta.NormNum.normNumAt` no longer exists
      anywhere in Mathlib/Batteries. The `norm_num`/`norm_num1` elaborators now live in
      `Mathlib/Tactic/NormNum/Core.lean` (`elabNormNum`, `NormNum.derive`). Reimplement
      `showByNormNum : Q(Prop) → MetaM Q($goal)` on the current API — e.g. elaborate
      `norm_num1` at a fresh metavariable via `Lean.Elab.Tactic`, or drive
      `NormNum.derive` + `Lean.Meta.mkExpectedTypeHint`-style proof assembly.
- [ ] **L157–158** — `reduceEval: failed to evaluate argument` on the `lhc`/`rhc` Qq
      ascriptions in `mkRowConflict`; check whether this is only a cascade of the
      `evalFin` proof type being wrong, once the above compile.
- [ ] **L235** — `example … := by sudoku_conflict` is the end-to-end smoke test
      (context parsing → `evalFin` → `mkRowConflict`); it fails because the tactic
      failed to elaborate upstream.
- [ ] Cleanup once green: remove debug `logInfo`s (`mkRowConflict`, `cellConflict`,
      `cellData:`, `after exfalos`), the stray `#check Sudoku.box_cases` and toy
      `example`s, then add `import LeanSudoku.STactic` to `LeanSudoku.lean` so
      `lake build` keeps it green.

### 2. Port the remaining gameplay tactics

Reference implementation: `LeanSudoku/STacticOld.lean` (Lean 3, starts with `#exit`,
kept verbatim as the spec). Current `STactic.lean` only has `sudoku_conflict` (and even
it only tries row conflicts — see the commented-out `<|>` chain).

- [ ] `row_logic` / `col_logic` / `box_logic` / `cell_logic` / `naked_single`
- [ ] pencil-mark handling: `pencil with p…`, `box_logic with p…` case-splitting
- [ ] `sudoku_assumption` / `sudoku_finish`
- [ ] parse `Sudoku.snyder₃` hypotheses (defined in `Basic.lean`, not yet recognised by
      `STactic.lean`'s parsers)

### 3. Port the board widget (`LeanSudoku/Widget.lean`)

Lean 3 widget/tactic-component code. Redesign against Lean 4's widget API
(ProofWidgets4, already in the dependency tree via Mathlib): render the 9×9 grid from
`Tactic.Sudoku.BoardInfo` (`cd`/`op`/`ip` cell & pencil-mark lists are already defined
in `STactic.lean`).

### 4. Make `scripts/gen.cpp` emit Lean 4

It still prints a Lean 3 game file (`import widget`, `open sudoku`,
`begin [show_sudoku] end`). Update the template to roughly:

```lean
import LeanSudoku.STactic

theorem play (s : Sudoku) (c00 : s.f (0, 0) = 8) … : … := by …
```

and add a generated example game file to the repo as a regression test.

### 5. CI / docs polish

- [ ] `.github/workflows/lean_action_ci.yml` only runs `leanprover/lean-action@v1`.
      Verify on push that it runs `lake exe cache get` (otherwise Mathlib builds from
      source and CI times out); add an explicit step/`build-args` if needed.
- [ ] Once step 1–2 land: flip the README "How to play" section from reference-material
      to working instructions, and un-mark the status table entries.
