from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours --
# meeting end time must be no later than 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap (busy) constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must not overlap,
    # i.e., either finish before busy_start or start after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Beverly's calendar: free all day (no constraints).

# Austin is free all day (no constraints).

# Rachel's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 16:30 -> [930, 990)
rachel_busy = [(540, 570), (630, 660), (720, 750), (810, 900), (930, 990)]
add_busy_constraints(solver, rachel_busy)

# Andrea's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 15:30 -> [840, 930)
# 16:00 to 17:00 -> [960, 1020)
andrea_busy = [(570, 690), (720, 810), (840, 930), (960, 1020)]
add_busy_constraints(solver, andrea_busy)

# Search for a valid start time.
solution_found = False
# Latest possible start time is 1020 - 30 = 990 minutes.
for t in range(540, 991):
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