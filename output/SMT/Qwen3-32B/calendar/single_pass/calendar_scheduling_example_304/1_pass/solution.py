import z3

# Initialize Z3 solver
solver = z3.Solver()

# Define start time as an integer (minutes since midnight)
start = z3.Int('start')
end = start + 30  # Meeting duration is 30 minutes

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting must end by 17:00, so start can be at most 990 (16:30)
solver.add(start >= 540)
solver.add(start <= 990)

# Janice's preference: meeting should start no later than 13:00 (780 minutes)
solver.add(start <= 780)

# Function to add non-overlapping constraints for busy intervals
def add_busy_constraints(busy_intervals):
    for b_start, b_end in busy_intervals:
        solver.add(z3.Or(end <= b_start, start >= b_end))

# Define busy intervals for each participant in minutes since midnight
christine_busy = [(570, 630), (720, 750), (780, 810), (870, 900), (960, 990)]
bobby_busy = [(720, 750), (870, 900)]
elizabeth_busy = [(540, 570), (690, 780), (780, 840), (900, 930), (960, 1020)]
tyler_busy = [(540, 660), (720, 750), (780, 810), (930, 960), (990, 1020)]
edward_busy = [(540, 570), (600, 660), (690, 840), (870, 930), (960, 1020)]

# Add constraints for each participant
add_busy_constraints(christine_busy)
add_busy_constraints(bobby_busy)
add_busy_constraints(elizabeth_busy)
add_busy_constraints(tyler_busy)
add_busy_constraints(edward_busy)

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    day = "Monday"
    start_time = f"{start_val//60:02d}:{start_val%60:02d}"
    end_time = f"{(start_val + 30)//60:02d}:{(start_val + 30)%60:02d}"
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")