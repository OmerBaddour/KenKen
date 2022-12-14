# src

Complete programs that serve some real, albeit limited, purpose.

`utils` contains utilities written for KenKen.

The bulk of the code was adapted from the Sudoku section of [this page](https://ericpony.github.io/z3py-tutorial/guide-examples.htm#sudoku)

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

## four_by_four_with_mult_div.py

Even more generic template than `four_by_four.py` as it also includes multiplication and division.

Specifically, this is a solver for https://www.kenkenpuzzle.com/game, PUZZLE NO. 153388, 4X4, HARD

To adapt this program for solving other 4x4 puzzles, replace all constraints with those for the specific problem instance.

- Constraints with addition are of the form [z3.And(X[a][b] + X[c][d] == y)]
- Constraints with subtraction are of the form [z3.And(z3_abs(X[a][b] - X[c][d]) == y)]
- Constraints with multiplication are of the form [z3.And(X[a][b] \* X[c][d] == y)]
- Constraints with division are of the form [divide_constraint(X[a][b], X[c][d], y)]

### Usage

Modify the source code to match the constraints of the 4x4 problem instance you'd like to solve

```
$ python four_by_four_with_mult_div.py
```

## n_by_n_metaprogrammer.py

Program for generating programs for nxn KenKen puzzles

Copy the output of this program into a new Python file, satisfy the TODO in the source code for adding constraints, and run that program to solve

### Usage

```
$ python n_by_n_metaprogrammer.py
```

Input `n` for your puzzle instance

## nine_by_nine.py

Reasonably generic template for solving 9x9 KenKen puzzles, generated by src/mvp/n_by_n_metaprogrammer.py with input 9

Specifically, this is a solver for https://www.kenkenpuzzle.com/game, PUZZLE NO. 74592, 9X9, HARD

Important note: the runtime for puzzles of this size and complexity is approximately 15 minutes

To adapt this program for solving other 9x9 puzzles, replace all constraints with those for the specific problem instance.

- Constraints with addition are of the form [z3.And(X[a][b] + X[c][d] == y)]
- Constraints with subtraction are of the form [z3.And(z3_abs(X[a][b] - X[c][d]) == y)]
- Constraints with multiplication are of the form [z3.And(X[a][b] \* X[c][d] == y)]
- Constraints with division are of the form [divide_constraint(X[a][b], X[c][d], y)]

## four_by_four_with_mult_div.py

`four_by_four_with_mult_div.py` with util functions for all constraints.

To adapt this program for solving other 4x4 puzzles, replace all constraints with those for the specific problem instance.

- Constraints with addition use sum_constraint
- Constraints with subtraction use minus_constraint
- Constraints with multiplication use product_constraint
- Constraints with division use division_constraint

### Usage

Modify the source code to match the constraints of the 4x4 problem instance you'd like to solve

```
$ python four_by_four_with_mult_div.py
```

## kenken_image_processor.ipynb

Screenshot of image of KenKen puzzle from https://www.kenkenpuzzle.com/game to solution! Follow the markdown at the top of the notebook for good information and usage instructions.
