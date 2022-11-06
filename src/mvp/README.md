## four_by_four.py

Reasonably generic template for solving 4x4 KenKen puzzles

Specifically, this is a solver for https://www.kenkenpuzzle.com/game, PUZZLE NO. 149259, 4X4, EASY

To adapt this program for solving other 4x4 puzzles, replace all constraints with those for the specific problem instance.

- Constraints with addition are of the form [z3.And(X[a][b] + X[c][d] == y)]
- Constraints with subtraction are of the form [z3.And(z3_abs(X[a][b] - X[c][d]) == y)]

### Usage

Modify the source code to match the constraints of the 4x4 problem instance you'd like to solve

```
$ python four_by_four.py
```
