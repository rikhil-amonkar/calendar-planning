from z3 import *

# Initialize the solver
solver = Solver()

# Add the distinct constraint (assuming 'category' is a dictionary of Z3 variables)
solver.add(Distinct(*category.values()))