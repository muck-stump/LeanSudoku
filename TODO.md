# TODO — Lean 4 port status

Handoff notes for continuing this port. Branch: `lean4-current-setup` (based on `main`).
Verified environment: Lean `v4.35.0`, Mathlib tag `v4.35.0`, Lake (bundled), elan ≥ 2.0.

Reproduce the current state from a fresh clone:

```sh
lake exe cache get && lake build   # exit 0; the expected warnings are the
                                   # Mathlib `module` hints and `Games/Easy1.lean`'s `sorry`
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
- [x] `LeanSudoku/STactic.lean` (board reading + `sudoku_conflict`) ported and part of
      the build:
  - `showByNormNum` → `showByDecide` on `Lean.Meta.mkDecideProof`
    (`Mathlib.Meta.NormNum.normNumAt` no longer exists);
  - `evalFin` returns a bare `Fin 9` (no bundled proof), with a `whnf` fallback route so
    `box_cases`' computed coordinates (`↑(3 * ↑(2 / 3) + 1)`), not just literal numerals,
    evaluate — wrapped in `try/ccatch`, since `deriveNat` throws rather than returning
    `none` when no rule applies;
  - `CellData` drops its `hr hc hv` fields and the `Fin.ne_of_mod_ne` detour (Qq's
    unquoter choked on the mixed `Q(ℕ) = Q(Fin 9)` ascriptions); `decide` closes
    `l.ce ≠ r.ce` directly;
  - conflict chain re-enabled: `row <|> col <|> cell <|> box`, plus `conflictWith` to
    search the context *and* extra (case-split) facts;
  - `parseCellData`/pencil parsers `guard (← isDefEq s s')` after pattern-matching, so
    they only accept facts about the sudoku in the goal.
- [x] `LeanSudoku/Tactics.lean` (gameplay tactics) ported:
  - goal recognition: `SudokuGoal` covers cell / `snyder` / `double` / `triple` goals,
    parsed through `~q()` patterns after `Qq.checkTypeQ target q(Prop)`;
  - `sudoku_assumption`, `sudoku_finish`, `row_logic`, `col_logic`, `box_logic`,
    `cell_logic`/`naked_single`, `pencil`, and the `with p₀ p₁ …` pencil-mark clause;
  - shared engine (`resolveMain`/`splitOr`/…): split the onto-lemma, close every branch
    by board contradiction or by matching the goal, fall back to splitting pencil marks
    (last-to-first, as in Lean 3).
  - smoke tests for every tactic at the bottom of the file; they all elaborate under
    `lake build`.
- [x] `scripts/gen.cpp` emits Lean 4 game files; `scripts/gen.sh` wraps
      compile-and-run; a checked-in example `Games/Easy1.lean` (generated from
      `scripts/easy1`) keeps the tooling honest via the `Games` lake library.
- [x] README: reproducible setup, updated repository layout, and working
      "How to play" instructions.
- [x] Board widget: `LeanSudoku/SudokuWidget.lean` renders `Tactic.Sudoku.BoardInfo`
      as an HTML table and hands it to ProofWidgets' `HtmlDisplayPanel` panel widget
      via `Lean.Widget.savePanelWidgetInfo` — proofwidgets is already reachable
      transitively through Mathlib, so the lakefile needed no change. Standalone
      `show_sudoku` tactic, plus every gameplay tactic auto-attaching the pre-move
      snapshot at its own span. (Lean 3's `[show_sudoku] … end` begin-block bracket
      has no direct Lean 4 analogue; per-tactic panels are the replacement.)
      Notes for the record: `elab_rules` patterns bind no `stx` — use `(← getRef)` —
      while `elab stx:"name"` does; a `do` block lifts statements across monads here,
      no `liftCoreM` exists for `TacticM`.

Remaining build output is the informational "imports `Mathlib.…` … consider adding
`module`" warning per Mathlib-importing module — harmless; adopting the module system
downstream is out of scope.

## Remaining next steps

### 1. Recognize `Sudoku.snyder₃` goals

`Basic.lean` defines `snyder₃`, but `parseSudokuGoal` only recognizes cell/snyder/
double/triple shapes, so tactics refuse a `s.snyder₃ …` goal. Add a `GoalKind` case +
`slots`/`wrapSlot` handling (three cells, same right-nested `Or` plumbing) — small and
mechanical, would slot in right after the pencil-mark pieces.

### 2. CI / docs polish

- [ ] `.github/workflows/lean_action_ci.yml` only runs `leanprover/lean-action@v1`.
      Verify on push that it runs `lake exe cache get` (otherwise Mathlib builds from
      source and CI times out); add an explicit step/`build-args` if needed. The
      `Games` library now builds in CI too — the expected warnings are the `module`
      hints and `Games/Easy1.lean`'s `sorry`.
- [ ] Consider tracking widget UX parity and any tactics the Lean 3 game had but the
      port does not (diff against `STacticOld.lean`).
