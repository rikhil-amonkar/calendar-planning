from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting interval [start, start+duration)
# does not overlap with any busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Richard's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#  11:30 to 12:00  -> [690, 720)
#  13:00 to 13:30  -> [780, 810)
#  16:00 to 16:30  -> [960, 990)
richard_busy = [(540, 570), (690, 720), (780, 810), (960, 990)]
add_busy_constraints(solver, richard_busy)

# Joseph's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#  11:30 to 12:00  -> [690, 720)
#  12:30 to 13:30  -> [750, 810)
#  14:00 to 14:30  -> [840, 870)
joseph_busy = [(570, 630), (690, 720), (750, 810), (840, 870)]
add_busy_constraints(solver, joseph_busy)

# Gabriel's busy intervals:
#   9:00 to 11:00  -> [540, 660)
#  11:30 to 12:00  -> [690, 720)
#  12:30 to 17:00  -> [750, 1020)
gabriel_busy = [(540, 660), (690, 720), (750, 1020)]
add_busy_constraints(solver, gabriel_busy)

# Brenda's busy intervals:
#   9:00 to 12:00  -> [540, 720)
#  12:30 to 16:30  -> [750, 990)
brenda_busy = [(540, 720), (750, 990)]
add_busy_constraints(solver, brenda_busy)

# Search for the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")