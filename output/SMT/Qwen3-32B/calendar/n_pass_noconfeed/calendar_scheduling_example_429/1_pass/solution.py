from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the Z3 solver
solver = Solver()

# Variable for the start time in minutes since midnight
s = Int('s')

# Add constraints for the meeting to be between 9:00 (540) and 17:00 - 30 min (990)
solver.add(And(s >= 540, s <= 990))

# Define each participant's busy intervals in minutes
participants_busy = {
    'Judy': [(780, 810), (960, 990)],
    'Olivia': [(600, 630), (720, 780), (840, 870)],
    'Jacqueline': [(600, 630), (900, 930)],
    'Laura': [(540, 600), (630, 720), (780, 810), (870, 900), (930, 1020)],
    'Tyler': [(540, 600), (660, 690), (750, 780), (840, 870), (930, 1020)],
    'Lisa': [(570, 630), (660, 690), (720, 750), (780, 810), (840, 870), (960, 1020)]
}

# Add constraints for each busy interval
for busy_list in participants_busy.values():
    for b_start, b_end in busy_list:
        solver.add(Or(s + 30 <= b_start, s >= b_end))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    start_time = model[s].as_long()
    end_time = start_time + 30
    start_str = min_to_time(start_time)
    end_str = min_to_time(end_time)
    print(f"{start_str}:{end_str} Monday")
else:
    print("No solution found")