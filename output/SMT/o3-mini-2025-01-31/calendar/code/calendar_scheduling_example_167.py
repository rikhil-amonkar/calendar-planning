from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function for busy intervals.
# For each busy interval [bs, be), the meeting [start, start+duration)
# should either completely finish before it starts, or start after it ends.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Marilyn's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 15:30 to 16:00 -> [930, 960)
marilyn_busy = [(630, 690), (720, 750), (930, 960)]
add_busy_constraints(solver, marilyn_busy)

# George is free the entire day, so no constraints.

# Stephanie's busy intervals:
# 10:30 to 12:30 -> [630, 750)
# 13:30 to 16:30 -> [810, 990)
stephanie_busy = [(630, 750), (810, 990)]
add_busy_constraints(solver, stephanie_busy)

# Kimberly's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 17:00 -> [930, 1020)
kimberly_busy = [(540, 630), (750, 780), (810, 900), (930, 1020)]
add_busy_constraints(solver, kimberly_busy)

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
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")