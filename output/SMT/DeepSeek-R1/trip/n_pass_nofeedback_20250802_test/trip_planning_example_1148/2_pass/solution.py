from z3 import *

def symmetric_equals(a, b, a_val, b_val):
    return Or([And(a == a_val, b == b_val), And(a == b_val, b == a_val)])

# Example usage (if needed in the larger program)
# s = Solver()
# a, b = Ints('a b')
# s.add(symmetric_equals(a, b, 1, 2))
# print(s.check())
# print(s.model())