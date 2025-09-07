from z3 import *

# Initialize solver
solver = Solver()

# Define start time variable (in minutes since midnight)
S = Int('S')

# Add constraints for work hours (9:00-17:00 => 540 to 1020 minutes)
solver.add(S >= 540)
solver.add(S <= 990)  # Since meeting is 30 min, S + 30 <= 1020 => S <= 990

# Define blocked intervals for each participant
bradley_blocked = [(570, 600), (750, 780), (810, 840), (930, 960)]
teresa_blocked = [(630, 660), (720, 750), (780, 810), (870, 900)]
elizabeth_blocked = [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)]
christian_blocked = [(540, 570), (630, 1020)]

# Add constraints for each participant's blocked intervals
for start, end in bradley_blocked:
    solver.add(Or(S + 30 <= start, S >= end))
for start, end in teresa_blocked:
    solver.add(Or(S + 30 <= start, S >= end))
for start, end in elizabeth_blocked:
    solver.add(Or(S + 30 <= start, S >= end))
for start, end in christian_blocked:
    solver.add(Or(S + 30 <= start, S >= end))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = start_time + 30

    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = to_time_str(start_time)
    end_str = to_time_str(end_time)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")