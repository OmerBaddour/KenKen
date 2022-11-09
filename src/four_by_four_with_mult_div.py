"""
Reasonably generic template for solving 4x4 KenKen puzzles

Specifically, this is a solver for https://www.kenkenpuzzle.com/game, PUZZLE NO. 153388, 4X4, HARD

To adapt this program for solving other 4x4 puzzles, replace all constraints with those for the specific problem instance.
- Constraints with addition are of the form [z3.And(X[a][b] + X[c][d] == y)]
- Constraints with subtraction are of the form [z3.And(z3_abs(X[a][b] - X[c][d]) == y)]
- Constraints with multiplication are of the form [z3.And(X[a][b] * X[c][d] == y)]
- Constraints with division are of the form [divide_constraint(X[a][b], X[c][d], y)]
"""

import z3


def z3_abs(x):
    """
    Absolute value of a z3 number

    Source: https://stackoverflow.com/questions/22547988/how-to-calculate-absolute-value-in-z3-or-z3py
    """
    return z3.If(x >= 0, x, -x)


def divide_constraint(X_i, X_j, ratio):
    """
    Ratio between two z3 numbers is constrained
    """
    return z3.Or(X_i / X_j == ratio, X_j / X_i == ratio)


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
    constraints.append([z3.And(z3_abs(X[0][0] - X[0][1]) == 3)])
    constraints.append([z3.And(X[0][2] * X[0][3] * X[1][2] == 24)])
    constraints.append([z3.And(z3_abs(X[1][0] - X[1][1]) == 2)])
    constraints.append([divide_constraint(X[1][3], X[2][3], 2)])
    constraints.append([z3.And(z3_abs(X[2][0] - X[3][0]) == 1)])    
    constraints.append([z3.And(z3_abs(X[2][1] - X[2][2]) == 1)])
    constraints.append([z3.And(X[3][1] + X[3][2] + X[3][3] == 8)])

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
