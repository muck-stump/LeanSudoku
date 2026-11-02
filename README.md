# Playing sudoku in the Lean theorem prover

![Screenshot](screenshot/screenshot.jpg)

*The original Lean 3 game (a VS Code widget). The Lean 4 port plays the same way,
and draws its board as an infoview panel — see [See the board](#see-the-board) —
the same picture, in any Lean 4 client.*

A Lean 4 port of Markus Himmel's [Lean 3 sudoku](https://github.com/TwoFX/sudoku).
You don't solve the grid on paper — in a file you *prove* that each cell contains
the right number, using tactics that encode ordinary sudoku solving strategies.

> **Status (work in progress):** the core library, the interactive gameplay tactics
> (`row_logic`, `col_logic`, `box_logic`, `cell_logic`/`naked_single`, pencil marks,
> `sudoku_assumption`, `sudoku_finish`), the game generator and the board widget
> (rendered as an infoview panel) all build on the current toolchain
> (Lean v4.35.0 + Mathlib v4.35.0). See [TODO.md](TODO.md) for exactly where the
> port stands.

## Getting started

### Prerequisites

* [`elan`](https://github.com/leanprover/elan) ≥ 2.0, the Lean toolchain manager.
  It automatically downloads the exact Lean version pinned in this repository the
  first time you run a `lake` command:

  ```sh
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

* (Optional, only for generating game files) a C++ compiler, e.g. `g++` or `clang++`.

Nothing else: you do not install Lean or Mathlib separately.

### Build

```sh
git clone https://github.com/muck-stump/LeanSudoku.git
cd LeanSudoku
lake exe cache get   # download prebuilt Mathlib (~minutes, once per checkout)
lake build           # build the LeanSudoku library and the Games check-in
```

`lake` resolves the toolchain from `lean-toolchain` (via `elan`) and all
dependencies from `lake-manifest.json`. Mathlib is fetched prebuilt, so nothing
compiles Mathlib from source.

Expected warnings, none of them failures: an unplayed game file reports
`declaration uses 'sorry'`, and each module that imports Mathlib prints an
informational "consider adding `module`" hint.

### How the build is pinned (reproducibility)

| File               | Role                                                            |
| ------------------ | --------------------------------------------------------------- |
| `lean-toolchain`   | exact Lean release used (`leanprover/lean4:v4.35.0`)            |
| `lakefile.toml`    | Mathlib requirement, pinned with `rev = "v4.35.0"`              |
| `lake-manifest.json` | exact commit of every transitive dependency — always commit it |

Mathlib tags correspond 1:1 to Lean releases, so `lean-toolchain` and the
Mathlib `rev` in `lakefile.toml` should always carry the same version number.

### Updating the toolchain

To move to a newer stable Lean release `vX.Y.Z`:

1. Set `lean-toolchain` to `leanprover/lean4:vX.Y.Z`.
2. Set the Mathlib `rev` in `lakefile.toml` to `vX.Y.Z`.
3. Run `lake update mathlib` (this also fetches the Mathlib cache).
4. Run `lake build`, fix any breakage, and commit the `lean-toolchain`,
   `lakefile.toml` and `lake-manifest.json` changes together.

### Editor setup

No project-specific plugin configuration is required: any Lean 4 LSP client that
respects `lean-toolchain` works.

**Neovim** with [lean.nvim](https://github.com/Julian/lean.nvim) — the setup this
port was exercised against:

* `lean.nvim` enables a `leanls` server whose `root_dir` detection finds this
  repo's `lakefile.toml` and, because one exists, starts **`lake serve`** — so
  `import LeanSudoku` and Mathlib imports resolve with zero setup. Opening any
  `.lean` file under the repo root is enough.
* The server is configured (`dependencyBuildMode = never`) to *never build*
  dependencies itself: run `lake build` after a fresh clone or after changing
  anything under `LeanSudoku/`, or imports will fail with a missing-olean error.
* After regenerating or renaming a file under `Games/`, dismiss the
  "imports out of date" notice with `:LeanRestartFile`.
* The infoview renders this project's panel widgets (board pictures — see
  *See the board* below) in the foldable *HTML Display* panel.

**VS Code** with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
(or another Lean 4 client) also works: the editor reads `lean-toolchain` and starts
the pinned toolchain automatically.

## Repository layout

| Path                         | What it is                                                     | Status      |
| ---------------------------- | -------------------------------------------------------------- | ----------- |
| `LeanSudoku/Basic.lean`      | sudoku definition and lemmas (rows, cols, boxes, pencil marks) | ✅ builds   |
| `LeanSudoku/STactic.lean`    | board reading and `sudoku_conflict`                            | ✅ builds   |
| `LeanSudoku/Tactics.lean`    | gameplay tactics (`row_logic`, …, `sudoku_finish`)             | ✅ builds   |
| `LeanSudoku/SudokuWidget.lean` | board picture as an infoview panel widget (`show_sudoku`)     | ✅ builds   |
| `LeanSudoku/STacticOld.lean` | original Lean 3 tactics, kept as the porting reference         | ⏸ reference only |
| `LeanSudoku/Widget.lean`     | original Lean 3 board widget (Lean 3 `tc` API)                 | ⏸ reference only |
| `scripts/gen.sh`, `gen.cpp`  | turn a grid into a game file                                   | ✅ emits Lean 4 |
| `Games/`                     | game files; `Games/Easy1.lean` is a checked-in example         | 🎮 play here |

## How to play

### Generate a game file

A game is a Lean file holding a theorem that packs the clue cells into one
`Givens s` hypothesis and whose conclusion is every cell of the solved grid.
Turn a grid (nine lines of nine integers, `0` = empty) into one:

```sh
scripts/gen.sh < scripts/easy1 > Games/MyGame.lean
```

The file builds right away — the proof body starts as `sorry` (a warning, not an
error) — so you can open it in your editor and start playing. `Games/Easy1.lean` is
such a game, generated from `scripts/easy1`.

The clue cells travel as *one* hypothesis: the file defines
`def Givens (s : Sudoku) : Prop := …` (one clue equation per line) and the
theorem takes `(g : Givens s)`, so the goal reads `g : Givens s` — one line —
instead of listing every clue above the target. The tactics and the board
widget unfold it while reading the context; `unfold Givens at g` if you want
to see the equations yourself.

How deep that goal prints is one build flag, not a property of each generated
file: `lakefile.toml` sets `pp.deepTerms.threshold = 6` under `[leanOptions]`,
so the 81-cell answer-key conjunction elides to `⋯` after a couple of cells
instead of filling ~50 infoview lines and pushing the board widget (rendered
below the goal — see [See the board](#see-the-board)) out of view. Raise the
number to read more of the answer key in the goal, lower it for shorter
goals — it is display-only. Every hypothesis prints in full at any setting —
your own moves and pencil marks exactly as you write them — and the board
widget already shows which cells are left. If you generate a game into some *other* project,
copy that line into its lakefile: without it, Lean's default threshold of
50 applies.

Lake only elaborates the games registered in `Games.lean`; after creating a new
file, either add `import Games.MyGame` there so `lake build` checks it, or check it
on its own with `lake env lean Games/MyGame.lean`. Your editor elaborates it
either way, since the language server never builds dependencies itself
(see *Editor setup*).

### Make a move

Cells are zero-indexed from the top left. You place the number `z` in cell `(x, y)` by saying

```lean
have cxy : s.f (x, y) = z := by <a tactic>
```

so each `have` records a move *and* the reason it is correct. There are five tactics
for a single cell:

* `row_logic` splits along the statement "there is a `z` somewhere in row `x`" and
  tries to find a conflict on the board for every position other than `(x, y)`
* `col_logic` and `box_logic` do the same for the column and the box of `(x, y)`
* `cell_logic` is like the others, but splits along the statement "there is a number in (x, y)"
* `naked_single` is a synonym for `cell_logic` to conform to usual sudoku terminology

When a *given* cell is all you need, `sudoku_assumption` closes the goal from the
context, and once every cell has been proven, `sudoku_finish` discharges the remaining
conjunction of the generated theorem. (`sudoku_conflict` runs the board-conflict
search on its own: it closes any goal for which the context alone is contradictory.)

A concrete opening line for the checked-in `Games/Easy1.lean` (replacing its
`sorry`):

```lean
  have c70 : s.f (7, 0) = 9 := by row_logic
  sorry
```

— the given cells rule out the filled slots of row 7, and the 9s already sitting in
columns 3, 6, 7 and 8 rule out the four empty ones, so `row_logic` forces
`(7, 0) = 9` from the givens alone. If a tactic *can't* yet finish a move it refuses
politely and lists the branches it could not rule out — that is the game telling you
which pencil marks you still need, not an error.

### See the board

You don't have to keep the grid on paper. Every move tactic (`row_logic`, `col_logic`,
`box_logic`, `cell_logic`/`naked_single`, `pencil`, `sudoku_assumption`) attaches a
picture of the board **as it looked before that move** as a widget panel in the
infoview: put the cursor on a tactic line and the panel shows

* each proven cell as a digit (large in a browser, bold everywhere)
* double/triple pencil marks in the cell centre, smaller and dimmed
* outer (Snyder) pencil marks as small dim digits
* 💥 in a cell whose context proves two different values (your pencil marks have
  gone wrong), and a faint `·` in cells not yet proven

Clues show up as digits just like proven moves: the widget reads them out of
`Givens s` through the same context reading the tactics use.

Box structure adapts to the renderer: a browser (VS Code) draws thick lines around
every 3×3 box, while lean.nvim's terminal renderer shades alternating boxes with a
colored checkerboard and separates columns with `│` — see
`LeanSudoku/SudokuWidget.lean` for how one markup drives both.

Stepping down your game file line by line therefore replays the board filling up.
(In lean.nvim the panel is the foldable *HTML Display* entry in the infoview; pin
it if you want it to stay visible.) An explicit `show_sudoku` tactic renders the
current position on its own, without making a move:

```lean
show_sudoku
```

There is also support for two kinds of pencil marks: Snyder notation on the edges of cells
and doubles and triples in the center of cells.

If you say

```lean
have p0 : s.snyder w x y z a
```

then you have to prove that there is an `a` in `(w, x)` or `(y, z)`. You will usually use
row, box or column logic for this.

If you say

```lean
have p1 : s.double x y a b
```

then you have to prove that there is either an `a` or a `b` in `(x, y)`.

Doing this will give you a pencil mark. To later use such a pencil mark in a deduction, you
can say things like `box_logic with p0 p1`, which for every possible position in the box will
first try to find an unconditional conflict and then split over `p0` and `p1` in the cases
where it gets stuck.

Finally, you can use `pencil with p0 p1` to make case distinctions over pencil marks only.

For hard sudokus, you'll want to formalize some actual sudoku theory. That lives in
`LeanSudoku/Basic.lean`.

## License

Apache 2.0, see [LICENSE](LICENSE). Originally written by Markus Himmel for Lean 3;
this is a work-in-progress port.
