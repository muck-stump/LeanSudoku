#include <array>
#include <vector>
#include <iostream>
using namespace std;

#define pb push_back
#define mp make_pair
#define eb emplace_back
#define all(a) begin(a), end(a)
#define has(a, b) (a.find(b) != a.end())
#define fora(i, n) for(int i = 0; i < n; i++)
#define forb(i, n) for(int i = 1; i <= n; i++)
#define forc(a, b) for(const auto &a : b)
#define ford(i, n) for(int i = n; i >= 0; i--)
#define maxval(t) numeric_limits<t>::max()
#define minval(t) numeric_limits<t>::min()
#define imin(a, b) a = min(a, b)
#define imax(a, b) a = max(a, b)
#define sz(x) (int)(x).size()
#define pvec(v) copy(all(v), ostream_iterator<decltype(v)::value_type>(cout, " "))

#define dbgs(x) #x << " = " << x
#define dbgs2(x, y) dbgs(x) << ", " << dbgs(y)
#define dbgs3(x, y, z) dbgs2(x, y) << ", " << dbgs(z)
#define dbgs4(w, x, y, z) dbgs3(w, x, y) << ", " << dbgs(z)

using ll = long long;
using ld = long double;

bool solve(vector<vector<int>> &s, int i, int j) {
	if (j == 9) { ++i; j = 0; }
	if (i == 9) return true;

	if (s[i][j] != 0) return solve(s, i, j + 1);

	forb(k, 9) {
		bool ok = true;
		fora(l, 9) if (s[i][l] == k) ok = false;
		fora(l, 9) if (s[l][j] == k) ok = false;
		fora(l, 3) fora(m, 3) {
			if (s[3 * (i / 3) + l][3 * (j / 3) + m] == k) ok = false;
		}
		if (!ok) continue;
		s[i][j] = k;
		if (solve(s, i, j + 1)) return true;
	}
	s[i][j] = 0;

	return false;
}

int main()
{
	ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	vector<vector<int>> s(9, vector<int>(9));

	fora(i, 9) fora(j, 9) {
		cin >> s[i][j];
	}

	cout << "import LeanSudoku\n\n";
	cout << "/-!\n";
	cout << "  A generated sudoku game.  Every cell of the grid has to be proven,\n";
	cout << "  one deduction at a time.  Start a line like\n\n";
	cout << "    have c00 : s.f (0, 0) = 8 := by row_logic\n\n";
	cout << "  (or `col_logic`, `box_logic`, `cell_logic`, `naked_single`, see\n";
	cout << "  README.md) in place of the `sorry` below, and close the whole board\n";
	cout << "  with `sudoku_finish`.\n\n";
	cout << "  The clue cells live behind one hypothesis, `g : Givens s`, so the\n";
	cout << "  goal shows one line instead of a wall of equations; the tactics and\n";
	cout << "  the board widget unfold it (`unfold Givens at g` to see it yourself).\n";
	cout << "-/\n\n";
	// How deep the conclusion below pretty-prints (eliding to `⋯`) is set by
	// `pp.deepTerms.threshold` in this repo's lakefile.toml: games carry no
	// option of their own, so the knob lives in exactly one place.
	// Emit the clue cells as one bundled hypothesis: the goal then displays a
	// single line (`g : Givens s`) instead of one hypothesis per clue, and the
	// tactics and the board widget project it back apart (factProofs).
	cout << "def Givens (s : Sudoku) : Prop :=\n";
	{
		vector<array<int, 3>> clues;
		fora(i, 9) fora (j, 9) if (s[i][j] != 0) clues.push_back({i, j, s[i][j]});
		fora(k, (int) clues.size()) {
			cout << "    s.f (" << clues[k][0] << ", " << clues[k][1] << ") = " << clues[k][2];
			cout << (k + 1 == (int) clues.size() ? "\n" : " ∧\n");
		}
		// a grid without clues is unplayable anyway, but stay valid Lean
		if (clues.empty()) cout << "    True\n";
	}
	cout << "\ntheorem play (s : Sudoku) (g : Givens s)";

	solve(s, 0, 0);

	cout << " :\n";

	fora(i, 9) fora(j, 9) {
		cout << "    s.f (" << i << ", " << j << ") = " << s[i][j];
		cout << ((i != 8 || j != 8) ? " ∧\n" : "\n");
	}

	cout << "    := by\n";
	cout << "  sorry\n";
}
