from z3 import *

# Create solver instance
s = Solver()

# Add the constraint to the solver
s.add(ForAll([i], Implies(And(i >= 0, i < 5, drink_vars[i] == root_beer_idx), 
                         Exists([j], And(j > i, j < 5, name_vars[j] == peter_idx)))))