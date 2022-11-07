"""
Program for generating programs for nxn KenKen puzzles

Copy the output of this program into a new Python file, satisfy the TODO in the source code for adding constraints, and run that program to solve
"""

if __name__ == "__main__":
    n = input("Puzzle dimension (e.g. 4 for 4x4): ")
    print(f"""import z3


def z3_abs(x):
    \"\"\"
    Absolute value of a z3 number

    Source: https://stackoverflow.com/questions/22547988/how-to-calculate-absolute-value-in-z3-or-z3py
    \"\"\"
    return z3.If(x >= 0, x, -x)


def divide_constraint(X_i, X_j, ratio):
    \"\"\"
    Ratio between two z3 numbers is constrained
    \"\"\"
    return z3.Or(X_i / X_j == ratio, X_j / X_i == ratio)


if __name__ == "__main__":

    # {n}x{n} matrix of integer variables
    X = [[z3.Int("x_%s_%s" % (i + 1, j + 1)) for j in range({n})] for i in range({n})]

    # each cell contains a value in {{1, ..., {n}}}
    cells_c = [z3.And(1 <= X[i][j], X[i][j] <= {n}) for i in range({n}) for j in range({n})]

    # each row contains a digit at most once
    rows_c = [z3.Distinct(X[i]) for i in range({n})]

    # each column contains a digit at most once
    cols_c = [z3.Distinct([X[i][j] for i in range({n})]) for j in range({n})]

    # constraints going left to right, top to bottom
    constraints = []
    # TODO add constraints

    kenken_c = cells_c + rows_c + cols_c
    for constraint in constraints:
        kenken_c += constraint

    # initialize with all empty cells
    instance = {tuple(tuple([0 for _ in range(int(n))]) for _ in range(int(n)))}
    instance_c = [
        z3.If(instance[i][j] == 0, True, X[i][j] == instance[i][j])
        for i in range({n})
        for j in range({n})
    ]

    s = z3.Solver()
    s.add(kenken_c + instance_c)
    if s.check() == z3.sat:
        m = s.model()
        r = [[m.evaluate(X[i][j]) for j in range({n})] for i in range({n})]
        z3.print_matrix(r)
    else:
        print("failed to solve")

    """)