"""
`four_by_four_with_mult_div.py` with util functions for all constraints.

Specifically, this is a solver for https://www.kenkenpuzzle.com/game, PUZZLE NO. 153388, 4X4, HARD

To adapt this program for solving other 4x4 puzzles, replace all constraints with those for the specific problem instance.
- Constraints with addition use sum_constraint
- Constraints with subtraction use minus_constraint
- Constraints with multiplication use product_constraint
- Constraints with division use division_constraint
"""

import z3

from utils.kenken import (division_constraint, minus_constraint,
                          product_constraint, sum_constraint)

if __name__ == "__main__":

    # 4x4 matrix of integer variables
    X = [[z3.Int("x_%s_%s" % (i + 1, j + 1)) for j in range(4)] for i in range(4)]

    # each cell contains a value in {1, ..., 4}
    cells_c = [z3.And(1 <= X[i][j], X[i][j] <= 4) for i in range(4) for j in range(4)]

    # each row contains a digit at most once
    rows_c = [z3.Distinct(X[i]) for i in range(4)]

    # each column contains a digit at most once
    cols_c = [z3.Distinct([X[i][j] for i in range(4)]) for j in range(4)]

    # constraints going left to right, top to bottom
    constraints = []
    constraints.append([minus_constraint(X[0][0], X[0][1], 3)])
    constraints.append([product_constraint([X[0][2], X[0][3], X[1][2]], 24)])
    constraints.append([minus_constraint(X[1][0], X[1][1], 2)])
    constraints.append([division_constraint(X[1][3], X[2][3], 2)])
    constraints.append([minus_constraint(X[2][0], X[3][0], 1)])    
    constraints.append([minus_constraint(X[2][1], X[2][2], 1)])
    constraints.append([sum_constraint([X[3][1], X[3][2], X[3][3]], 8)])

    kenken_c = cells_c + rows_c + cols_c
    for constraint in constraints:
        kenken_c += constraint

    # initialize with all empty cells
    instance = ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0))
    instance_c = [
        z3.If(instance[i][j] == 0, True, X[i][j] == instance[i][j])
        for i in range(4)
        for j in range(4)
    ]

    s = z3.Solver()
    s.add(kenken_c + instance_c)
    if s.check() == z3.sat:
        m = s.model()
        r = [[m.evaluate(X[i][j]) for j in range(4)] for i in range(4)]
        z3.print_matrix(r)
    else:
        print("failed to solve")
