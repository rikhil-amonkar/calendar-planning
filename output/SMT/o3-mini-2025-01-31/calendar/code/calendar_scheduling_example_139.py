from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for a given busy interval [bs, be),
# the meeting [start, start+duration) must either end on or before bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jose's busy intervals:
#   9:00 to 9:30 -> [540, 570]
#   12:00 to 12:30 -> [720, 750]
#   13:00 to 14:00 -> [780, 840]
jose_busy = [(540, 570), (720, 750), (780, 840)]
add_busy_constraints(solver, jose_busy)

# Sean's busy intervals:
#   10:30 to 11:00 -> [630, 660]
#   12:30 to 13:30 -> [750, 810]
#   14:30 to 15:00 -> [870, 900]
sean_busy = [(630, 660), (750, 810), (870, 900)]
add_busy_constraints(solver, sean_busy)

# Denise's busy intervals:
#   9:00 to 9:30   -> [540, 570]
#   10:00 to 11:30 -> [600, 690]
#   13:00 to 13:30 -> [780, 810]
#   14:00 to 14:30 -> [840, 870]
#   15:00 to 17:00 -> [900, 1020]
denise_busy = [(540, 570), (600, 690), (780, 810), (840, 870), (900, 1020)]
add_busy_constraints(solver, denise_busy)

# Amanda's busy intervals:
#   9:00 to 10:00 -> [540, 600]
#   10:30 to 11:30 -> [630, 690]
#   12:00 to 17:00 -> [720, 1020]
amanda_busy = [(540, 600), (630, 690), (720, 1020)]
add_busy_constraints(solver, amanda_busy)

# Find a valid meeting time by scanning possible start times.
solution_found = False
# Meeting can start at times t from 540 to 1020-duration=990 (inclusive)
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