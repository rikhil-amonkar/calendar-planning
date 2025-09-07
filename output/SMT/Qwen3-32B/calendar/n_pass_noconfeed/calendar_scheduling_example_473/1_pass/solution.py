import z3

# Create a Z3 solver instance
solver = z3.Solver()

# Define the start time as an integer variable (in minutes since midnight)
start = z3.Int('start')

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes), meeting duration is 30 minutes
solver.add(z3.And(start >= 540, start <= 990))  # start <= 990 ensures end time is <= 1020

# Define participants' busy intervals in minutes since midnight
participants = {
    'Gregory': [(540, 570), (690, 720)],
    'Jonathan': [(540, 570), (720, 750), (780, 810), (900, 960), (990, 1020)],
    'Barbara': [(600, 630), (810, 840)],
    'Jesse': [(600, 660), (750, 870)],
    'Alan': [(570, 660), (690, 750), (780, 930), (960, 1020)],
    'Nicole': [(540, 630), (690, 720), (750, 810), (840, 1020)],
    'Catherine': [(540, 630), (720, 810), (900, 930), (960, 990)]
}

# Add constraints for each participant's busy intervals
for intervals in participants.values():
    for s_int, e_int in intervals:
        solver.add(z3.Or(start + 30 <= s_int, start >= e_int))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    start_time = f"{(start_val // 60):02d}:{(start_val % 60):02d}"
    end_time = f"{(start_val // 60 + (start_val % 60 + 30) // 60):02d}:{( (start_val % 60 + 30) % 60 ):02d}"
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found")