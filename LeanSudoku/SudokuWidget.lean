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

Two rendering targets have to work from the same markup:

* a browser (e.g. the VS Code infoview): CSS provides the borders — thin ones
  everywhere, thick ones on the 3×3 box lines — the fixed cell size, and the
  big digits;
* lean.nvim's terminal renderer (`tui.html`): it turns the `<table>` into one
  text line per `<tr>` with the cells joined by ` │ `. It ignores `border`,
  `width`, `height` and `font-size`, but honours `color`, `background-color`
  and `font-weight`. Content must therefore be a `<span>` (inline) and never a
  `<div>` (`Tag.div` is block-level: one newline per cell — a 81-line stack).
  Alternating 3×3 boxes get a light background tint so the box structure stays
  visible in the terminal, and empty cells carry a faint `·` so every column has
  width ≥ 1 (zero-width cells would make both the tint and the padding vanish).
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

/-- One cell's contents: the shown digit, the pencil marks, 💥 for a contradictory
cell, or a faint `·` for an unknown one, as `(text, cssStyle)`. -/
private def cellView (r c : Nat) (bi : BoardInfo) : String × String :=
  match cellDigits r c bi with
  -- exactly one known value: the big digit, as in the Lean 3 widget
  | [v] => (digitStr v, "font-weight:bold;font-size:26px;")
  -- more than one value in one cell: the context is contradictory
  | _ :: _ => ("💥", "font-size:26px;")
  -- no cell proven yet: pencil marks, inner (double/triple) ones taking
  -- precedence over outer (Snyder) ones
  | [] =>
    match innerDigits r c bi with
    | ds@(_ :: _) => (String.intercalate " " (ds.map digitStr), "color:#57606a;font-size:15px;")
    | [] =>
      match outerDigits r c bi with
      | ds@(_ :: _) => (String.intercalate " " (ds.map digitStr), "color:#777e85;")
      | [] => ("·", "color:#c9ccd1;font-size:26px;")

/-- One `td`: browser CSS frame (see the module docstring for how the terminal
renderer treats it) plus one inline `<span>` with the cell's text. -/
private def cellHtml (r c : Nat) (bi : BoardInfo) : Html :=
  let frame :=
    "box-sizing:border-box;border:1px solid #c9ccd1;" ++
    (if r % 3 = 0 then "border-top:3px solid #24292f;" else "") ++
    (if r % 3 = 2 then "border-bottom:3px solid #24292f;" else "") ++
    (if c % 3 = 0 then "border-left:3px solid #24292f;" else "") ++
    (if c % 3 = 2 then "border-right:3px solid #24292f;" else "") ++
    (if (r / 3 + c / 3) % 2 = 0 then "background-color:#eef1f4;" else "") ++
    "width:42px;height:42px;padding:0 8px;text-align:center;vertical-align:middle;"
  let (text, style) := cellView r c bi
  Html.element "td" #[(("style", Json.str frame))]
    #[Html.element "span" #[(("style", Json.str style))] #[Html.text text]]

/-- The 9×9 board as an HTML table. The `tr`/`td` shape matters: lean.nvim's
terminal renderer draws one line per row and joins the cells with ` │ `. -/
def boardTable (bi : BoardInfo) : Html :=
  let rows : Array Html := (List.range 9).toArray.map fun r ↦
    Html.element "tr" #[] ((List.range 9).toArray.map fun c ↦ cellHtml r c bi)
  Html.element "table" #[(("style", Json.str "border-collapse:collapse;"))] rows

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
