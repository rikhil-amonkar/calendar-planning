from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting [start, start+duration) must
    # either end on or before bs, or start at or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Linda's busy intervals:
#   10:00 to 11:30 -> [600, 690]
#   12:00 to 12:30 -> [720, 750]
#   13:00 to 14:00 -> [780, 840]
linda_busy = [(600, 690), (720, 750), (780, 840)]
add_busy_constraints(solver, linda_busy)

# Samantha's busy intervals:
#   10:30 to 11:00 -> [630, 660]
#   16:00 to 16:30 -> [960, 990]
samantha_busy = [(630, 660), (960, 990)]
add_busy_constraints(solver, samantha_busy)

# Ralph's busy intervals:
#   9:00 to 10:00   -> [540, 600]
#   10:30 to 12:00  -> [630, 720]
#   12:30 to 13:30  -> [750, 810]
#   14:00 to 15:00  -> [840, 900]
#   16:30 to 17:00  -> [990, 1020]
ralph_busy = [(540, 600), (630, 720), (750, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, ralph_busy)

# Katherine's busy intervals:
#   10:00 to 12:30 -> [600, 750]
#   13:30 to 14:00 -> [810, 840]
#   14:30 to 15:00 -> [870, 900]
#   15:30 to 16:00 -> [930, 960]
katherine_busy = [(600, 750), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, katherine_busy)

# Search for a valid meeting time by iterating over all possible start times.
solution_found = False
# The meeting can start at any time t from 540 to 1020 - duration = 990
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")