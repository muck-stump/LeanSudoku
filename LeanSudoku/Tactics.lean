import LeanSudoku.Basic
import LeanSudoku.STactic

set_option relaxedAutoImplicit false

namespace Tactic.Sudoku

open Lean Meta Elab Tactic
open scoped Qq
open Fin.NatCast

/-! ## Gameplay tactics

A move in the game is written as

```lean
have c05 : s.f (0, 5) = 3 := by row_logic
```

The logic tactics discharge such a goal by case-splitting one of the onto-lemmas
from `Basic.lean` (`row_cases`, `col_cases`, `box_cases`, `cell_cases`) and
ruling out all branches but one: either by a contradiction with the cells on the
board (an `sudoku_conflict`-style argument, possibly using further pencil marks),
or because the surviving branch is exactly the goal and closes directly.
-/

/-- The kinds of statement the gameplay tactics accept as goals. -/
inductive GoalKind where
  | /-- `s.f (r, c) = v` -/ cell
  | /-- `s.snyder s r₀ c₀ r₁ c₁ v`: one of the two cells holds `v` -/ snyder
  | /-- `s.double s r c v₁ v₂`: the cell holds `v₁` or `v₂` -/ double
  | /-- `s.triple s r c v₁ v₂ v₃`: the cell holds one of `v₁`, `v₂`, `v₃` -/ triple
  deriving BEq

/-- A goal statement in recognised shape: `slots` holds one `(row, column, value)`
triple per disjunct — a cell goal has the single slot `#[(r, c, v)]`, a pencil-mark
goal one slot per alternative. -/
structure SudokuGoal where
  /-- which of the four shapes the goal has -/
  kind : GoalKind
  /-- the sudoku the goal talks about -/
  s : Q(Sudoku)
  /-- the cells (or candidate cells) the goal is about -/
  slots : Array (Q(Fin 9) × Q(Fin 9) × Q(Fin 9))

/-- The cell the player wants to fill in (`slots[0]`). -/
def SudokuGoal.root (g : SudokuGoal) : Q(Fin 9) × Q(Fin 9) × Q(Fin 9) :=
  g.slots[0]!

/-- Recognises the four goal shapes the gameplay tactics understand. -/
def parseSudokuGoal (target : Expr) : MetaM (Option SudokuGoal) := do
  -- `~q()` patterns only match `Q(α)`-typed expressions, so first view the `Expr`
  -- `target` as a term of type `Q(Prop)` (all tactic goals we handle are `Prop`s).
  let some t ← Qq.checkTypeQ target q(Prop) | return none
  match t with
  | ~q(Sudoku.f $s ($r, $c) = $v) =>
    return some { kind := .cell, s, slots := #[(r, c, v)] }
  | ~q(Sudoku.snyder $s $r₀ $c₀ $r₁ $c₁ $v) =>
    return some { kind := .snyder, s, slots := #[(r₀, c₀, v), (r₁, c₁, v)] }
  | ~q(Sudoku.double $s $r $c $v₁ $v₂) =>
    return some { kind := .double, s, slots := #[(r, c, v₁), (r, c, v₂)] }
  | ~q(Sudoku.triple $s $r $c $v₁ $v₂ $v₃) =>
    return some { kind := .triple, s, slots := #[(r, c, v₁), (r, c, v₂), (r, c, v₃)] }
  | _ => return none

/-- The proposition "slot `i` holds": `s.f (r, c) = v`. -/
def slotType (g : SudokuGoal) (i : Nat) : Expr :=
  let s := g.s
  let (r, c, v) := g.slots[i]!
  q(Sudoku.f $s ($r, $c) = $v)

/-- Wraps a proof of slot `i` into a proof of the (unfolded) goal — for a cell goal
that is the identity; pencil-mark goals need `Or.inl`/`Or.inr` on the right path.
The disjunctions are right-nested to match how `a ∨ b ∨ c` parses. -/
def wrapSlot (g : SudokuGoal) (i : Nat) (p : Expr) : Expr :=
  match g.kind, i with
  | .cell, _ => p
  | .snyder, 0 | .double, 0 =>
      mkApp3 (mkConst ``Or.inl) (slotType g 0) (slotType g 1) p
  | .snyder, _ | .double, _ =>
      mkApp3 (mkConst ``Or.inr) (slotType g 0) (slotType g 1) p
  | .triple, 0 =>
      mkApp3 (mkConst ``Or.inl) (slotType g 0)
        (mkApp2 (mkConst ``Or) (slotType g 1) (slotType g 2)) p
  | .triple, 1 =>
      mkApp3 (mkConst ``Or.inr) (slotType g 0)
        (mkApp2 (mkConst ``Or) (slotType g 1) (slotType g 2))
        (mkApp3 (mkConst ``Or.inl) (slotType g 1) (slotType g 2) p)
  | .triple, _ =>
      mkApp3 (mkConst ``Or.inr) (slotType g 0)
        (mkApp2 (mkConst ``Or) (slotType g 1) (slotType g 2))
        (mkApp3 (mkConst ``Or.inr) (slotType g 1) (slotType g 2) p)

/-- Searches for a proof of `target` among the given cell hypotheses. -/
def proveFromCells (g : SudokuGoal) (target : Expr) (cands : List CellData) :
    MetaM (Option Expr) := do
  for i in [0 : g.slots.size] do
    let ty := slotType g i
    for d in cands do
      if ← isDefEq (← inferType d.e) ty then
        let pr := wrapSlot g i d.e
        if ← isDefEq (← inferType pr) target then
          return some pr
  return none

/-- Closes the goal if a cell hypothesis in the context already proves it (pencil-mark
goals are matched against their disjuncts). -/
elab "sudoku_assumption" : tactic => do
  let goal ← getMainGoal
  liftMetaM do goal.withContext do
    let s ← getSudoku
    let cd ← getCellData s
    let target ← goal.getType
    let some g ← parseSudokuGoal target
      | throwError "goal is not a sudoku statement:{indentExpr target}"
    match ← proveFromCells g target cd with
    | some pr => goal.assign pr
    | none => throwError "no hypothesis in the context proves{indentExpr target}"

/-- Plays out the goal: repeatedly closes conjuncts from the context (`sudoku_assumption`)
or splits the final conjunction of all 81 cells (`constructor`). -/
elab "sudoku_finish" : tactic => do
  evalTactic (← `(tactic| repeat (first | sudoku_assumption | constructor)))

/-! ### Smoke tests for the gameplay tactics -/

-- `sudoku_assumption` finishes a goal already present in the context.
example (s : Sudoku) (h0 : s.f (0, 0) = 1) : s.f (0, 0) = 1 := by
  sudoku_assumption

-- ... and wraps it into a pencil-mark goal.
example (s : Sudoku) (h0 : s.f (0, 0) = 1) : s.snyder 0 0 0 1 1 := by
  sudoku_assumption

-- `sudoku_finish` plays out the whole generated-game conclusion from the given cells.
example (s : Sudoku) (h00 : s.f (0, 0) = 1) (h01 : s.f (0, 1) = 2) :
    s.f (0, 0) = 1 ∧ s.f (0, 1) = 2 := by
  sudoku_finish

end Tactic.Sudoku
