from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: adds constraints ensuring that the meeting interval [start, start+duration)
# does not overlap a given busy interval [busy_start, busy_end).
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Benjamin's busy intervals:
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:30 -> [870, 930)
benjamin_busy = [(750, 810), (870, 930)]
add_busy_constraints(solver, benjamin_busy)

# Philip's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
philip_busy = [(690, 720), (750, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, philip_busy)

# Jessica's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:30 to 15:00  -> [810, 900)
# 16:00 to 16:30  -> [960, 990)
jessica_busy = [(570, 660), (690, 720), (810, 900), (960, 990)]
add_busy_constraints(solver, jessica_busy)

# Ashley's busy intervals:
# 10:00 to 12:00  -> [600, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:30  -> [900, 990)
ashley_busy = [(600, 720), (750, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, ashley_busy)

# We need to find the earliest valid meeting time available for everyone.
solution_found = False
# The meeting start should be from 9:00 (540 minutes) up to 17:00 - duration (990 minutes)
for t in range(540, 991):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")