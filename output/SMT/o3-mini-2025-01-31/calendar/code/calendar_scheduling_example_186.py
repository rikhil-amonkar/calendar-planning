from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')

# Meeting must start and end within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting time [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Richard and Frances are free all day, so there are no busy intervals for them.

# Andrea's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#  10:30 to 14:00  -> [630, 840)
#  14:30 to 16:00  -> [870, 960)
#  16:30 to 17:00  -> [990, 1020)
andrea_busy = [(570, 600), (630, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, andrea_busy)

# Cheryl's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#  11:00 to 12:30  -> [660, 750)
#  13:00 to 14:00  -> [780, 840)
#  14:30 to 15:00  -> [870, 900)
#  16:00 to 16:30  -> [960, 990)
cheryl_busy = [(540, 630), (660, 750), (780, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, cheryl_busy)

# Search for the earliest meeting time.
solution_found = False
for t in range(540, 1020 - duration + 1):  # t in [540, 990]
    solver.push()  # save the solver state
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
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")