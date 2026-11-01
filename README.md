# Playing sudoku in the Lean theorem prover

![Screenshot](screenshot/screenshot.jpg)

A Lean 4 port of Markus Himmel's [Lean 3 sudoku](https://github.com/TwoFX/sudoku).
You don't solve the grid on paper — in a file you *prove* that each cell contains
the right number, using tactics that encode ordinary sudoku solving strategies.

> **Status (work in progress):** the core library (`LeanSudoku/Basic.lean`) builds
> cleanly on a current toolchain (Lean v4.35.0 + Mathlib v4.35.0). The interactive
> gameplay tactics and the board widget are still being ported from Lean 3 —
> see [TODO.md](TODO.md) for exactly where the port stands.

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
lake build           # build the LeanSudoku library
```

`lake` resolves the toolchain from `lean-toolchain` (via `elan`) and all
dependencies from `lake-manifest.json`. Mathlib is fetched prebuilt, so nothing
compiles Mathlib from source.

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

Open the repository folder in VS Code with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
(or another Lean 4 client). The editor reads `lean-toolchain` and starts the pinned
toolchain automatically; no project-specific editor configuration is required.

## Repository layout

| Path                        | What it is                                                  | Status      |
| --------------------------- | ----------------------------------------------------------- | ----------- |
| `LeanSudoku/Basic.lean`     | sudoku definition and lemmas (rows, cols, boxes, pencil marks) | ✅ builds   |
| `LeanSudoku/STactic.lean`   | gameplay tactics (`sudoku_conflict`, …)                      | 🚧 partial port, not yet in the build |
| `LeanSudoku/STacticOld.lean` | original Lean 3 tactics, kept as the porting reference        | ❌ unported |
| `LeanSudoku/Widget.lean`    | board-display widget                                         | ❌ unported (Lean 3) |
| `scripts/gen.cpp`           | turns a grid into a game file                                | 🚧 still emits Lean 3 syntax |

## How to play

*This describes the game as it worked in the Lean 3 version; it is the behaviour
the tactics above are being ported to restore (see [TODO.md](TODO.md)).*

Cells are zero-indexed from the top left. You place the number `z` in cell `(x, y)` by saying

```lean
have cxy : s.f (x, y) = z
```

but now you have to prove why this is the case. There are four main tactics for that:

* `box_logic` splits along the statement "there is a z somewhere in the box of (x, y)" and
  tries to find a conflict on the board for every position other than (x, y)
* `row_logic` and `col_logic` are the same as `box_logic`, but (you guessed it) for rows and
  columns rather than boxes
* `cell_logic` is like the others, but splits along the statement "there is a number in (x, y)"
* `naked_single` is a synonym for `cell_logic` to conform to usual sudoku terminology

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
