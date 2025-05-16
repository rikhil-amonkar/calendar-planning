from z3 import *

# Define the start time variable in minutes since midnight
S = Int('S')

# Define the constraints for the meeting time
constraints = [
    S >= 540,  # Earliest start time: 9:00
    S <= 960   # Latest start time to allow a 60-minute meeting: 16:00
]

# Define the blocked intervals for James and John in minutes
blocked_intervals = [
    (690, 720),  # James: 11:30-12:00
    (870, 900),  # James: 14:30-15:00
    (570, 660),  # John: 9:30-11:00
    (690, 720),  # John: 11:30-12:00
    (750, 810),  # John: 12:30-13:30
    (870, 990)   # John: 14:30-16:30
]

# Add constraints for each blocked interval
for A, B in blocked_intervals:
    constraints.append(Or(S + 60 <= A, S >= B))

# Create the solver and add all constraints
solver = Solver()
solver.add(constraints)

# Check for satisfiability
if solver.check() == sat:
    model = solver.model()
    s_val = model[S].as_long()
    start_h = s_val // 60
    start_m = s_val % 60
    end = s_val + 60
    end_h = end // 60
    end_m = end % 60
    print(f"Monday, {start_h:02d}:{start_m:02d} - {end_h:02d}:{end_m:02d}")
else:
    print("No solution found.")