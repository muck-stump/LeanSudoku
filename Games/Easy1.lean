import LeanSudoku

/-!
  A generated sudoku game.  Every cell of the grid has to be proven,
  one deduction at a time.  Start a line like

    have c00 : s.f (0, 0) = 8 := by row_logic

  (or `col_logic`, `box_logic`, `cell_logic`, `naked_single`, see
  README.md) in place of the `sorry` below, and close the whole board
  with `sudoku_finish`.

  The clue cells live behind one hypothesis, `g : Givens s`, so the
  goal shows one line instead of a wall of equations; the tactics and
  the board widget unfold it (`unfold Givens at g` to see it yourself).
-/

def Givens (s : Sudoku) : Prop :=
    s.f (0, 1) = 7 ∧
    s.f (0, 4) = 2 ∧
    s.f (0, 5) = 6 ∧
    s.f (0, 6) = 5 ∧
    s.f (1, 1) = 4 ∧
    s.f (1, 3) = 9 ∧
    s.f (1, 6) = 7 ∧
    s.f (1, 7) = 8 ∧
    s.f (2, 0) = 2 ∧
    s.f (2, 2) = 8 ∧
    s.f (2, 3) = 4 ∧
    s.f (2, 7) = 9 ∧
    s.f (3, 2) = 1 ∧
    s.f (3, 5) = 3 ∧
    s.f (3, 6) = 9 ∧
    s.f (3, 7) = 4 ∧
    s.f (4, 0) = 6 ∧
    s.f (4, 2) = 5 ∧
    s.f (4, 3) = 1 ∧
    s.f (4, 4) = 7 ∧
    s.f (5, 1) = 3 ∧
    s.f (5, 6) = 1 ∧
    s.f (5, 8) = 7 ∧
    s.f (6, 0) = 5 ∧
    s.f (6, 4) = 9 ∧
    s.f (6, 6) = 4 ∧
    s.f (6, 7) = 3 ∧
    s.f (7, 1) = 2 ∧
    s.f (7, 2) = 4 ∧
    s.f (7, 4) = 5 ∧
    s.f (7, 5) = 8 ∧
    s.f (8, 3) = 7 ∧
    s.f (8, 7) = 5 ∧
    s.f (8, 8) = 9

theorem play (s : Sudoku) (g : Givens s) :
    s.f (0, 0) = 3 ∧
    s.f (0, 1) = 7 ∧
    s.f (0, 2) = 9 ∧
    s.f (0, 3) = 8 ∧
    s.f (0, 4) = 2 ∧
    s.f (0, 5) = 6 ∧
    s.f (0, 6) = 5 ∧
    s.f (0, 7) = 1 ∧
    s.f (0, 8) = 4 ∧
    s.f (1, 0) = 1 ∧
    s.f (1, 1) = 4 ∧
    s.f (1, 2) = 6 ∧
    s.f (1, 3) = 9 ∧
    s.f (1, 4) = 3 ∧
    s.f (1, 5) = 5 ∧
    s.f (1, 6) = 7 ∧
    s.f (1, 7) = 8 ∧
    s.f (1, 8) = 2 ∧
    s.f (2, 0) = 2 ∧
    s.f (2, 1) = 5 ∧
    s.f (2, 2) = 8 ∧
    s.f (2, 3) = 4 ∧
    s.f (2, 4) = 1 ∧
    s.f (2, 5) = 7 ∧
    s.f (2, 6) = 3 ∧
    s.f (2, 7) = 9 ∧
    s.f (2, 8) = 6 ∧
    s.f (3, 0) = 7 ∧
    s.f (3, 1) = 8 ∧
    s.f (3, 2) = 1 ∧
    s.f (3, 3) = 2 ∧
    s.f (3, 4) = 6 ∧
    s.f (3, 5) = 3 ∧
    s.f (3, 6) = 9 ∧
    s.f (3, 7) = 4 ∧
    s.f (3, 8) = 5 ∧
    s.f (4, 0) = 6 ∧
    s.f (4, 1) = 9 ∧
    s.f (4, 2) = 5 ∧
    s.f (4, 3) = 1 ∧
    s.f (4, 4) = 7 ∧
    s.f (4, 5) = 4 ∧
    s.f (4, 6) = 8 ∧
    s.f (4, 7) = 2 ∧
    s.f (4, 8) = 3 ∧
    s.f (5, 0) = 4 ∧
    s.f (5, 1) = 3 ∧
    s.f (5, 2) = 2 ∧
    s.f (5, 3) = 5 ∧
    s.f (5, 4) = 8 ∧
    s.f (5, 5) = 9 ∧
    s.f (5, 6) = 1 ∧
    s.f (5, 7) = 6 ∧
    s.f (5, 8) = 7 ∧
    s.f (6, 0) = 5 ∧
    s.f (6, 1) = 1 ∧
    s.f (6, 2) = 7 ∧
    s.f (6, 3) = 6 ∧
    s.f (6, 4) = 9 ∧
    s.f (6, 5) = 2 ∧
    s.f (6, 6) = 4 ∧
    s.f (6, 7) = 3 ∧
    s.f (6, 8) = 8 ∧
    s.f (7, 0) = 9 ∧
    s.f (7, 1) = 2 ∧
    s.f (7, 2) = 4 ∧
    s.f (7, 3) = 3 ∧
    s.f (7, 4) = 5 ∧
    s.f (7, 5) = 8 ∧
    s.f (7, 6) = 6 ∧
    s.f (7, 7) = 7 ∧
    s.f (7, 8) = 1 ∧
    s.f (8, 0) = 8 ∧
    s.f (8, 1) = 6 ∧
    s.f (8, 2) = 3 ∧
    s.f (8, 3) = 7 ∧
    s.f (8, 4) = 4 ∧
    s.f (8, 5) = 1 ∧
    s.f (8, 6) = 2 ∧
    s.f (8, 7) = 5 ∧
    s.f (8, 8) = 9
    := by
  sorry
