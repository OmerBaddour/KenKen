import math
from typing import List

import z3


def sum_constraint(list_elts: List[z3.Int], total: int) -> z3.And:
    """
    Z3 sum constraint on a list of Z3 Ints.

    list_elts: list of ints of type z3.Int
    total: sum of list_elts

    returns a Z3 constraint that the sum of list_elts must equal total
    """
    return z3.And(sum(list_elts) == total)


def z3_absolute(z3_int: z3.Int) -> z3.If:
    """
    Absolute value of a z3 number

    Source: https://stackoverflow.com/questions/22547988/how-to-calculate-absolute-value-in-z3-or-z3py
    """
    return z3.If(z3_int >= 0, z3_int, -z3_int)


def minus_constraint(z3_int_1: z3.Int, z3_int_2: z3.Int, difference: int) -> z3.And:
    """
    Z3 minus constraint on a pair of Z3 Ints.

    z3_int_1: z3.Int
    z3_int_2: z3.Int
    difference: absolute difference between z3_int_1 and z3_int_2

    returns a Z3 constraint that the absolute difference between z3_int_1 and z3_int_2 must equal difference
    """
    absolute_difference = z3_absolute(z3_int_1 - z3_int_2)
    return z3.And(absolute_difference == difference)


def product_constraint(list_elts: List[z3.Int], product: int) -> z3.And:
    """
    Z3 product constraint on a list of Z3 Ints.

    list_elts: list of ints of type z3.Int
    product: product of list_elts

    returns a Z3 constraint that the product of list_elts must equal product
    """
    return z3.And(math.prod(list_elts) == product)


def division_constraint(z3_int_1: z3.Int, z3_int_2: z3.Int, ratio: int) -> z3.Or:
    """
    Z3 divide constraint on a pair of Z3 Ints.

    z3_int_1: z3.Int
    z3_int_2: z3.Int
    ratio: ratio of z3_int_1 and z3_int_2

    returns a Z3 constraint that the ratio of z3_int_1 and z3_int_2 must equal ratio
    """
    return z3.Or(z3_int_1 / z3_int_2 == ratio, z3_int_2 / z3_int_1 == ratio)