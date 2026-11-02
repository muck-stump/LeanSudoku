import LeanSudoku.Basic

set_option relaxedAutoImplicit false

-- def List.mfirst' {M : Type → Type v} [Monad M] {α : Type} [Inhabited α] (f : α → M Bool) : List α → M α
-- | [] => return default
-- | (a::as) => do
--   let r ← f a
--   if r then return a else List.mfirst' f as

-- def List.mfiltermap {M : Type u → Type v} [Monad M] {α : Type w} {β : Type u}
--   (f : α → M (Option β)) : List α → M (List β) := sorry

-- | [] := return []
-- | (x::xs) := do
--     y ← f x,
--     r ← list.mfiltermap xs,
--     match y with
--     | none := return r
--     | some z := return (z::r)
--     end

def Lean.LocalContext.toList (ctx : Lean.LocalContext) : List Lean.LocalDecl :=
  ctx.foldr List.cons []
namespace Tactic.Sudoku

open Lean Meta Elab Tactic
open scoped Qq

-- The `NatCast (Fin n)` instance lives in the `Fin.NatCast` scope; opening it here
-- makes numeral coordinates of type `Fin 9` (as they occur in `Basic.lean`'s
-- conflict lemmas) elaborate the same way as inside `Basic.lean`.
open Fin.NatCast

def getSudoku : MetaM Q(Sudoku) := do
  let lctx ← getLCtx
  let board? ← lctx.findDeclM? fun decl ↦ do
    let ⟨1, ~q(Sudoku), ~q($s)⟩ ← Qq.inferTypeQ decl.toExpr | return none
    return some s
  match board? with
  | some board => return board
  | none => throwError m!"could not find sudoku variable"

structure CellData where
  /-- The row, column and value of the filled cell, as *values* in `0 … 8`. -/
  (row col val : Fin 9)
  /-- The hypothesis itself: a proof of `s.f (row, col) = val`. -/
  (e : Expr)
  (re ce ve : Q(Fin 9))

instance : ToMessageData CellData where
  toMessageData | {row, col, val, e, ..} => m!"({e} : s.f ({row}, {col}) = {val})"

structure OuterPencilData where
  (row₀ col₀ row₁ col₁ val : Fin 9)
  (e : Expr)

structure InnerPencilData where
  (row col : Fin 9)
  (vals : List (Fin 9))
  (e : Expr)

structure BoardInfo where
  (cd : List CellData)
  (op : List OuterPencilData)
  (ip : List InnerPencilData)

/-- Evaluates an expression `e` of type `Fin 9` (e.g. a coordinate or a cell value
written as a numeral in the goal or in a hypothesis) to its value in `0 … 8`.
Fails if the expression is not a ground numeral of that shape.

The coordinates produced by `box_cases` are computed terms such as
`↑(3 * ↑(2 / 3) + 1)` rather than plain numerals, so several strategies are tried:
`norm_num`-style evaluation directly, after whnf, and finally by evaluating the
underlying `Fin.val` to a natural literal. -/
def evalFin (e : Q(Fin 9)) : MetaM (Option (Fin 9)) := do
  let viaNormNum (e : Q(Fin 9)) : MetaM (Option (Fin 9)) := do
    let ⟨natLit, _⟩ ← Mathlib.Meta.NormNum.deriveNat e (q(Fin.instAddMonoidWithOne 9))
    let some n ← getNatValue? natLit | return none
    -- `deriveNat` may report `9` for the element `(9 : Fin 9) = 0`; reduce modulo 9
    if h : n % 9 < 9 then return some ⟨n % 9, h⟩ else return none
  let guarded (x : Q(Fin 9)) : MetaM (Option (Fin 9)) :=
    try viaNormNum x catch _ => return none
  let whnfOpt : MetaM (Option Q(Fin 9)) :=
    try return some (← whnf e) catch _ => return none
  -- 1. plain numerals
  if let some v ← guarded e then return some v
  -- 2. numerals after reducing the computed coordinate arithmetic
  if let some e' ← whnfOpt then
    if let some v ← guarded e' then return some v
    -- 3. the `Fin.val` of a constructor form, evaluated to a natural literal
    let n ← try whnf (← mkAppM ``Fin.val #[e']) catch _ => return none
    let some k ← getNatValue? n | return none
    if h : k % 9 < 9 then return some ⟨k % 9, h⟩ else return none
  else
    return none

def parseCellData (s : Q(Sudoku)) (e : Expr) : MetaM (Option CellData) := do
  let ⟨0, ~q(Sudoku.f $s' ($er, $ec) = $ev), e⟩ ← Qq.inferTypeQ e | return none
  guard (← isDefEq s s')
  let some r ← evalFin er | return none
  let some c ← evalFin ec | return none
  let some v ← evalFin ev | return none
  return some ⟨r, c, v, e, er, ec, ev⟩

def parseOuterPencilData (s : Q(Sudoku)) (e : Expr) : MetaM (Option OuterPencilData) := do
  let ⟨0, ~q(Sudoku.snyder $s' $er₀ $ec₀ $er₁ $ec₁ $ev), e⟩ ← Qq.inferTypeQ e | return none
  guard (← isDefEq s s')
  let some r₀ ← evalFin er₀ | return none
  let some c₀ ← evalFin ec₀ | return none
  let some r₁ ← evalFin er₁ | return none
  let some c₁ ← evalFin ec₁ | return none
  let some v ← evalFin ev | return none
  return some ⟨r₀, c₀, r₁, c₁, v, e⟩

def parseInnerPencilData₂ (s : Q(Sudoku)) (e : Expr) : MetaM (Option InnerPencilData) := do
  let ⟨0, ~q(Sudoku.double $s' $er $ec $ev₁ $ev₂), e⟩ ← Qq.inferTypeQ e | return none
  guard (← isDefEq s s')
  let some r ← evalFin er | return none
  let some c ← evalFin ec | return none
  let some v₁ ← evalFin ev₁ | return none
  let some v₂ ← evalFin ev₂ | return none
  return some ⟨r, c, [v₁, v₂], e⟩

def parseInnerPencilData₃ (s : Q(Sudoku)) (e : Expr) : MetaM (Option InnerPencilData) := do
  let ⟨0, ~q(Sudoku.triple $s' $er $ec $ev₁ $ev₂ $ev₃), e⟩ ← Qq.inferTypeQ e | return none
  guard (← isDefEq s s')
  let some r ← evalFin er | return none
  let some c ← evalFin ec | return none
  let some v₁ ← evalFin ev₁ | return none
  let some v₂ ← evalFin ev₂ | return none
  let some v₃ ← evalFin ev₃ | return none
  return some ⟨r, c, [v₁, v₂, v₃], e⟩

def parseInnerPencilData (s : Q(Sudoku)) (e : Expr) : MetaM (Option InnerPencilData) := do
  match ← parseInnerPencilData₂ s e with
  | some d => return some d
  | none => parseInnerPencilData₃ s e

/-- The individual facts recorded by one hypothesis.

A hypothesis that already names a fact we know how to read — a cell equation
or a pencil mark (`parseCellData`, `parse*PencilData`) — is returned untouched:
its own proof term is what conflict arguments and `proveFromCells` are built
from. Anything else whose type *reduces to a conjunction* is split into its
conjuncts by projection (`And.left` / `And.right`). That is how the generated
games' clue bundle — one hypothesis `g : Givens s`, one line in the goal
display — reaches the tactics and the board widget as the individual cell
equations they expect, without the goal ever being touched: only the proof
term in hand is projected, so the compact display survives board reading.

Recognizable facts are leaves even when their type unfolds to a `∧` — the
parsing order is what keeps a pencil-mark proof (whose body is an `Or` anyway)
available to its own parser. -/
partial def factProofs (s : Q(Sudoku)) (p : Expr) : MetaM (List Expr) := do
  if (← parseCellData s p).isSome
      || (← parseOuterPencilData s p).isSome
      || (← parseInnerPencilData s p).isSome then
    return [p]
  let t ← try whnf (← inferType p) catch _ => return [p]
  if t.isAppOfArity ``And 2 then
    try
      let left ← mkAppM ``And.left #[p]
      let right ← mkAppM ``And.right #[p]
      return (← factProofs s left) ++ (← factProofs s right)
    catch _ => return [p]
  return [p]

/-- Every hypothesis of the context as a list of fact proofs, unpacking
bundled hypotheses (see `factProofs`) on the way. -/
def unpackedFacts (s : Q(Sudoku)) : MetaM (List Expr) := do
  let lCtx ← getLCtx
  let ps ← lCtx.toList.mapM (fun decl => factProofs s decl.toExpr)
  return ps.flatten

def getCellData (s : Q(Sudoku)) : MetaM (List CellData) := do
  (← unpackedFacts s).filterMapM (parseCellData s)

def getOuterPencilData (s : Q(Sudoku)) : MetaM (List OuterPencilData) := do
  (← unpackedFacts s).filterMapM (parseOuterPencilData s)

def getInnerPencilData (s : Q(Sudoku)) : MetaM (List InnerPencilData) := do
  (← unpackedFacts s).filterMapM (parseInnerPencilData s)

def getBoardInfo (s : Q(Sudoku)) : MetaM BoardInfo := do
  let cellData ← getCellData s
  let outerPencilData ← getOuterPencilData s
  let innerPencilData ← getInnerPencilData s
  return ⟨cellData, outerPencilData, innerPencilData⟩

/-- Proves a *ground* fact (an equation or inequality between literal numerals, possibly
behind `%`, `/`, casts or `Fin` projections) by evaluating `decide`.

This replaces `norm_num`, whose MetaM entry point (`normNumAt`) no longer exists in
Mathlib v4.35.0. All the facts this is used for are closed by kernel computation, so
deciding them is both simpler and more robust than invoking `norm_num`. -/
def showByDecide (goal : Q(Prop)) : MetaM Q($goal) := do
  let proof ← Lean.Meta.mkDecideProof goal
  unless ← isDefEq (← inferType proof) goal do
    throwError "bug in Tactic.Sudoku: failed to prove ground fact:{indentExpr goal}"
  return proof

/-- Two hypotheses that put the same value in the same row at different columns
contradict the row-bijection. -/
def mkRowConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  guard (l.row = r.row)
  guard (l.val = r.val)
  guard (l.col ≠ r.col)
  let neProof ← showByDecide q($l.ce ≠ $r.ce)
  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($l.re, $r.ce) = $l.ve) := r.e
  return q(Sudoku.row_conflict $s $le $re $neProof)

def mkColConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  guard (l.row ≠ r.row)
  guard (l.val = r.val)
  guard (l.col = r.col)
  let neProof ← showByDecide q($l.re ≠ $r.re)
  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($r.re, $l.ce) = $l.ve) := r.e
  return q(Sudoku.col_conflict $s $le $re $neProof)

def mkCellConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  guard (l.row = r.row)
  guard (l.val ≠ r.val)
  guard (l.col = r.col)
  let neProof ← showByDecide q($l.ve ≠ $r.ve)
  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($l.re, $l.ce) = $r.ve) := r.e
  return q(Sudoku.cell_conflict $s $le $re $neProof)

def mkBoxConflict (s : Q(Sudoku)) (l r : CellData) : MetaM Q(False) := do
  guard (l.val = r.val)
  guard (l.row / 3 = r.row / 3)
  guard (l.col / 3 = r.col / 3)
  guard (l.row ≠ r.row ∨ l.col ≠ r.col)

  let rowEqProof ← showByDecide q(($l.re : Nat) / 3 = $r.re / 3)
  let colEqProof ← showByDecide q(($l.ce : Nat) / 3 = $r.ce / 3)

  let orProof ← if l.row ≠ r.row then
    let neProof ← showByDecide q($l.re ≠ $r.re)
    pure <| show Q($l.re ≠ $r.re ∨ $l.ce ≠ $r.ce) from q(Or.inl $neProof)
  else
    let neProof ← showByDecide q($l.ce ≠ $r.ce)
    pure <| show Q($l.re ≠ $r.re ∨ $l.ce ≠ $r.ce) from q(Or.inr $neProof)

  let le : Q(Sudoku.f $s ($l.re, $l.ce) = $l.ve) := l.e
  let re : Q(Sudoku.f $s ($r.re, $r.ce) = $l.ve) := r.e
  return q(Sudoku.box_conflict $s $le $re $rowEqProof $colEqProof $orProof)

/-- Tries `f` on all pairs of values in `l`, returning upon the first success. -/
def _root_.List.firstPairM [Alternative m] (l : List α) (f : α → α → m β) : m β :=
  l.firstM fun left => l.firstM fun right => f left right

def rowConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkRowConflict s)

def colConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkColConflict s)

def cellConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkCellConflict s)

def boxConflict (s : Q(Sudoku)) (cd : List CellData) : MetaM Q(False) :=
  cd.firstPairM (mkBoxConflict s)

/-- Searches for a contradiction between the known cells `cd` and the additional
facts `extra` (typically hypotheses introduced by a case split or pencil marks). -/
def conflictWith (s : Q(Sudoku)) (cd : List CellData) (extra : List Expr) : MetaM Q(False) := do
  let ds ← extra.filterMapM (parseCellData s)
  let all := ds ++ cd
  rowConflict s all <|> colConflict s all <|> cellConflict s all <|> boxConflict s all

def conflict : TacticM Unit :=
  liftMetaFinishingTactic fun goal => do
    let s ← getSudoku
    let cd ← getCellData s
    let falseGoal ← goal.exfalso
    let proof ← conflictWith s cd []
    falseGoal.assign proof

elab "sudoku_conflict" : tactic => conflict

example (s : Sudoku) (h1 : s.f (1, 1) = 1) (h2 : s.f (1, 2) = 1) : False := by
  sudoku_conflict

example (s : Sudoku) (h1 : s.f (1, 1) = 1) (h2 : s.f (4, 1) = 1) : False := by
  sudoku_conflict

example (s : Sudoku) (h1 : s.f (1, 1) = 1) (h2 : s.f (0, 0) = 1) : False := by
  sudoku_conflict

example (s : Sudoku) (h1 : s.f (1, 1) = 1) (h2 : s.f (1, 1) = 2) : False := by
  sudoku_conflict

-- Bundled clue hypotheses (a generated game's `g : Givens s`) are read exactly
-- like individual cell hypotheses: `factProofs` projects the conjunction apart
-- in proof terms and `getCellData` sees every clue.
def bundled (s : Sudoku) : Prop := s.f (1, 1) = 1 ∧ s.f (1, 2) = 1

example (s : Sudoku) (g : bundled s) : False := by
  sudoku_conflict

end Tactic.Sudoku
