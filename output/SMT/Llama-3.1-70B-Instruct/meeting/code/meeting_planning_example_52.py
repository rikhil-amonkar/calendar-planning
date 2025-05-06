from z3 import *

# Define variables
start_time = 9 * 60  # Convert to minutes
barbara_start = 13 * 60 + 15  # Convert to minutes
barbara_end = 18 * 60 + 15  # Convert to minutes

travel_time = {
    ('Russian Hill', 'Richmond District'): 14,
    ('Richmond District', 'Russian Hill'): 13,
}

# Define variables for meeting times
barbara_meet = Int('barbara_meet')

# Define variables for travel times
rh_rd = Int('rh_rd')
rd_rh = Int('rd_rh')

# Create solver
s = Solver()

# Add constraints
s.add(barbara_meet >= 45)

s.add(barbara_meet + rh_rd <= barbara_end - barbara_start)

s.add(rh_rd >= travel_time[('Russian Hill', 'Richmond District')])
s.add(rd_rh >= travel_time[('Richmond District', 'Russian Hill')])

# Optimize
s.maximize(barbara_meet)

# Check solution
if s.check() == sat:
    m = s.model()
    print("SOLUTION:")
    print("Meet Barbara for", m[barbara_meet], "minutes")
else:
    print("No solution found")