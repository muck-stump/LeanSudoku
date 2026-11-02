import LeanSudoku.STactic
import ProofWidgets.Component.HtmlDisplay

/-! # The sudoku board widget

The Lean 4 port of `LeanSudoku/Widget.lean` (Lean 3): renders the board from the
current context as an infoview *panel widget* — given cells as big digits, inner
(double/triple) pencil marks in the cell centre, outer (Snyder) pencil marks as
small digits, thick lines between 3×3 boxes, and 💥 on a cell whose context proves
two different values.

Mechanism: `Lean.Widget.savePanelWidgetInfo` attaches an HTML payload at a
tactic's syntax span; the client displays it whenever the cursor is on that
tactic. We reuse ProofWidgets' `HtmlDisplayPanel`, which has a hand-written
renderer in `lean.nvim` (`lean/widgets/ProofWidgets/HtmlDisplayPanel.lua`), so
this is editor-agnostic across the Lean 4 infoviews.

As in the Lean 3 widget, digits are stored `mod 9` (the digit 9 elaborates to
`(9 : Fin 9) = 0`), so `0` is printed as `9`.
-/

namespace Tactic.Sudoku

open Lean ProofWidgets
open Meta Elab Tactic

/-- Print a stored cell value (`0 … 8`) as the digit `1 … 9` it stands for. -/
def digitStr (v : Nat) : String :=
  toString (if v = 0 then 9 else v)

/-- The values proven to sit in cell `(n, m)`, deduplicated (more than one means
the context is contradictory). -/
def cellDigits (n m : Nat) (bi : BoardInfo) : List Nat :=
  (bi.cd.filterMap fun cd ↦
    if cd.row.val = n ∧ cd.col.val = m then some cd.val.val else none).eraseDups

/-- The values of the *outer* (two-cell, Snyder) pencil marks touching `(n, m)`. -/
def outerDigits (n m : Nat) (bi : BoardInfo) : List Nat :=
  (bi.op.filterMap fun op ↦
    if (op.row₀.val = n ∧ op.col₀.val = m) ∨ (op.row₁.val = n ∧ op.col₁.val = m)
    then some op.val.val
    else none).eraseDups

/-- The candidates written *into* cell `(n, m)` by a double or triple pencil mark. -/
def innerDigits (n m : Nat) (bi : BoardInfo) : List Nat :=
  match bi.ip.find? fun ip ↦ ip.row.val = n ∧ ip.col.val = m with
  | some ip => ip.vals.map (·.val)
  | none => []

private def digitsHtml (digits : List Nat) (style : String) : Html :=
  Html.element "div" #[(("style", Json.str style))]
    (digits.toArray.map fun v ↦
      Html.element "span" #[("style", Json.str "margin:0 1px;")] #[Html.text (digitStr v)])

/-- One `td`: thin borders everywhere, thick ones on 3×3 box boundaries. -/
private def cellHtml (r c : Nat) (bi : BoardInfo) : Html :=
  let frame :=
    "box-sizing:border-box;border:1px solid #c9ccd1;" ++
    (if r % 3 = 0 then "border-top:3px solid #24292f;" else "") ++
    (if r % 3 = 2 then "border-bottom:3px solid #24292f;" else "") ++
    (if c % 3 = 0 then "border-left:3px solid #24292f;" else "") ++
    (if c % 3 = 2 then "border-right:3px solid #24292f;" else "")
  let box := "width:42px;height:42px;text-align:center;vertical-align:middle;padding:0;"
  let content : Html :=
    match cellDigits r c bi with
    -- no cell proven yet: show pencil marks (inner ones take precedence), else nothing
    | [] =>
      match innerDigits r c bi with
      | [] => digitsHtml (outerDigits r c bi)
                "display:flex;flex-wrap:wrap;justify-content:center;align-self:flex-end;font-size:11px;color:#57606a;"
      | vs => digitsHtml vs
                "display:flex;justify-content:center;font-size:15px;letter-spacing:1px;color:#42484f;"
    -- exactly the one known value, as in the Lean 3 widget
    | [v] => digitsHtml [v] "font-size:26px;font-weight:600;"
    -- more than one value in one cell: the context is contradictory
    | _ => Html.element "div" #[] #[Html.text "💥"]
  Html.element "td" #[("style", Json.str (frame ++ box))] #[content]

/-- The 9×9 board as an HTML table. -/
def boardTable (bi : BoardInfo) : Html :=
  let rows : Array Html := (List.range 9).toArray.map fun r ↦
    Html.element "tr" #[] ((List.range 9).toArray.map fun c ↦ cellHtml r c bi)
  Html.element "table" #[
      ("style",
        Json.str "border-collapse:collapse;font-family:ui-monospace,'Cascadia Mono',monospace;")
    ] rows

/-- Reads the board out of the given goal's context and renders it. -/
def currentBoardHtml (g : MVarId) : MetaM Html :=
  g.withContext do
    let s ← getSudoku
    return boardTable (← getBoardInfo s)

/-- Save `html` as a panel widget attached to the tactic `stx`. -/
def saveBoardPanel (html : Html) (stx : Syntax) : TacticM Unit := do
  Lean.Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

/-- Display the board of the current context (given cells and pencil marks) as a
widget panel in the infoview. Put the cursor on this tactic to see the picture. -/
elab stx:"show_sudoku" : tactic => do
  let main ← getMainGoal
  saveBoardPanel (← liftMetaM (currentBoardHtml main)) stx

-- Example: the widget is display-only; it only has to elaborate.
set_option linter.unusedTactic false in
example (s : Sudoku) (h01 : s.f (0, 1) = 7) (hp : s.double 1 0 4 5) : True := by
  show_sudoku
  trivial

end Tactic.Sudoku
