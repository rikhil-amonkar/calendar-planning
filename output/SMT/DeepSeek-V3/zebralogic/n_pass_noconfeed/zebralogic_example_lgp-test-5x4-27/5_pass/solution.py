from z3 import *

# Create solver instance
s = Solver()

# Declare the variables used in quantifiers
i = Int('i')
j = Int('j')

# Define the arrays and constants that were missing
n = 5  # Assuming array size
drink_vars = [Int(f'drink_{k}') for k in range(n)]
name_vars = [Int(f'name_{k}') for k in range(n)]

# Define the index constants (assuming these are integer values)
root_beer_idx = Int('root_beer_idx')
peter_idx = Int('peter_idx')

# Add the constraint to the solver
s.add(ForAll([i], Implies(And(i >= 0, i < 5, drink_vars[i] == root_beer_idx), 
                         Exists([j], And(j > i, j < 5, name_vars[j] == peter_idx)))))