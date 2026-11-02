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

/-- Which of the four onto-lemmas from `Basic.lean` a logic tactic case-splits. -/
inductive Logic where
  | /-- `row_cases`: the goal's value occurs somewhere in the goal's row -/ row

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

/-- Which goals each logic tactic accepts. -/
def Logic.allowed (l : Logic) (k : GoalKind) : Bool :=
  match l, k with
  | .row, .cell => true
  | _, _ => false

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

/-- Tries to close goal `g` using the cells known from the context `cd` plus the
extra facts `stems`: first by contradiction on the board, then by matching one of
the stems against the goal. -/
def resolveGoal (s : Q(Sudoku)) (cd : List CellData) (stems : List Expr) (g : MVarId) :
    MetaM Bool := g.withContext do
  if let some fp ← (some <$> conflictWith s cd stems) <|> pure none then
    let falseGoal ← g.exfalso
    falseGoal.assign fp
    return true
  let target ← g.getType
  let some goal ← parseSudokuGoal target | return false
  let scds ← stems.filterMapM (parseCellData s)
  match ← proveFromCells goal target scds with
  | some pr => g.assign pr; return true
  | none => return false

/-- Runs `resolveGoal` on every open branch `(goal, extra facts)`, returning those
that could not be closed. -/
def resolveAll (s : Q(Sudoku)) (cd : List CellData) (branches : Array (MVarId × Array Expr)) :
    MetaM (Array (MVarId × Array Expr)) := do
  let mut open_ := #[]
  for (g, stems) in branches do
    unless ← resolveGoal s cd stems.toList g do
      open_ := open_.push (g, stems)
  return open_

/-- Finds the local hypothesis named `n` in the context of goal `g`. -/
def findHyp (g : MVarId) (n : Name) : MetaM (Option FVarId) :=
  g.withContext do
    return ((← getLCtx).findFromUserName? n).map (·.fvarId)

/-- Case-splits the hypothesis `f` (whose type unfolds to a nested `Or`) inside `g`,
returning every leaf branch together with the proof hypothesis the leaf introduces. -/
partial def splitOr (g : MVarId) (f : FVarId) : MetaM (Array (MVarId × Expr)) := do
  -- run the whole walk under the context of the goal being split: the hypothesis
  -- (and later the case payloads) are only declared there
  g.withContext do
    let ty ← whnf (← f.getType)
    if ty.isAppOfArity ``Or 2 then
      let mut out := #[]
      for sub in ← g.cases f do
        let payload := sub.subst.apply sub.fields[0]!
        if payload.isFVar then
          out := out ++ (← splitOr sub.mvarId payload.fvarId!)
        else
          out := out.push (sub.mvarId, payload)
      return out
    else
      return #[(g, Expr.fvar f)]

/-- The disjunction that the given logic tactic case-splits. -/
def caseProof (l : Logic) (g : SudokuGoal) : MetaM Expr := do
  let s := g.s
  let (r, c, v) := g.root
  match l with
  | .row => pure q(Sudoku.row_cases $s $r $v)

/-- Shared engine: optionally case-split `disj?` (an onto-lemma proof) in the main
goal, then repeatedly try to close every branch against the board, splitting the
pencil marks in `pencils` (last to first, as in the Lean 3 version) whenever the
cheaper arguments leave a branch open. Returns the goals that remain open. -/
def resolveMain (main : MVarId) (disj? : Option Expr) (pencils : Array Name) :
    MetaM (List MVarId) :=
  main.withContext do
    let s ← getSudoku
    let cd ← getCellData s
    let mut open_ : Array (MVarId × Array Expr) ←
      match disj? with
      | none => pure #[(main, #[])]
      | some pr => do
        let (disjF, goal₁) ← main.note `h pr
        let branches ← splitOr goal₁ disjF
        pure (branches.map fun (b, leaf) => (b, #[leaf]))
    open_ ← resolveAll s cd open_
    for p in pencils.reverse do
      if open_.isEmpty then break
      let mut next := #[]
      let mut found := false
      for (b, stems) in open_ do
        if let some pf ← findHyp b p then
          found := true
          for (b₂, leaf) in ← splitOr b pf do
            next := next.push (b₂, stems.push leaf)
        else
          next := next.push (b, stems)
      unless found do throwError "unknown hypothesis `{p}`"
      open_ ← resolveAll s cd next
    return (open_.map (·.1)).toList

/-- The shared implementation of the logic tactics: recognise the goal, build the
corresponding onto-lemma proof, and hand over to `resolveMain`. -/
def logicMain (main : MVarId) (l : Logic) (pencils : Array Name) : MetaM (List MVarId) :=
  main.withContext do
    let target ← main.getType
    let some g ← parseSudokuGoal target
      | throwError "I don't recognize the goal:{indentExpr target}"
    unless Logic.allowed l g.kind do
      throwError "this tactic does not apply to a goal of this shape:{indentExpr target}"
    resolveMain main (some (← caseProof l g)) pencils

/-- Shared entry point for the logic tactics: run `logicMain` on the main goal and
make its surviving branches the new goals. -/
def runLogic (l : Logic) (pencils : Array Name) : TacticM Unit := do
  let main ← getMainGoal
  replaceMainGoal (← liftMetaM (logicMain main l pencils))

/-- Splits the fact that the goal's value occurs somewhere in the goal's row
(`row_cases`) and closes every position but the goal's own cell by contradiction. -/
elab "row_logic" : tactic => runLogic .row #[]

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

-- `row_logic`: everything else in row 0 is filled in, so the goal cell is forced.
example (s : Sudoku) (h0 : s.f (0, 0) = 1) (h1 : s.f (0, 1) = 3) (h2 : s.f (0, 2) = 2)
    (h4 : s.f (0, 4) = 5) (h5 : s.f (0, 5) = 6) (h6 : s.f (0, 6) = 7)
    (h7 : s.f (0, 7) = 8) (h8 : s.f (0, 8) = 0) : s.f (0, 3) = 4 := by
  row_logic

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
