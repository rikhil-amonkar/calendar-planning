from z3 import *

# Initialize the solver
solver = Solver()

# Define the start time as an integer variable (minutes since midnight)
S = Int('S')

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# The meeting duration is 1 hour, so S must be <= 960 (16:00)
solver.add(S >= 540)
solver.add(S <= 960)

# James's blocked times in minutes
james_blocked = [(690, 720), (870, 900)]
for b_start, b_end in james_blocked:
    solver.add(Or(S + 60 <= b_start, b_end <= S))

# John's blocked times in minutes
john_blocked = [(570, 660), (690, 720), (750, 780), (870, 990)]
for b_start, b_end in john_blocked:
    solver.add(Or(S + 60 <= b_start, b_end <= S))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    s_val = model[S].as_long()
    
    # Convert start and end times to HH:MM format
    start_h, start_m = divmod(s_val, 60)
    end_h, end_m = divmod(s_val + 60, 60)
    
    # Format with leading zeros
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")