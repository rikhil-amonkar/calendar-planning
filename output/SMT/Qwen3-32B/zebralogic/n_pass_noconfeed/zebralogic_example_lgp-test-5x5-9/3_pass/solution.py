from z3 import *

# Initialize the solver
s = Solver()

# Assume eric_pos, drink, and tea are already defined elsewhere in your code
# For example:
# eric_pos = Int('eric_pos')
# drink = [Int(f'drink_{i}') for i in range(6)]  # assuming 6 drinks
# tea = Int('tea')

# Eric can't be in the 5th house (index 4)
for i in range(4):
    s.add(Implies(eric_pos == i, drink[i + 1] == tea))