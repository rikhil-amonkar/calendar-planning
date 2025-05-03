from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for each busy interval.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must either finish
    # at or before busy_start, or start at or after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Hannah is free all day; no busy intervals.

# Austin's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 12:00 to 12:30  -> [720, 750)
# 16:30 to 17:00  -> [990, 1020)
austin_busy = [(540, 600), (720, 750), (990, 1020)]
add_busy_constraints(solver, austin_busy)

# Donna's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 13:00  -> [630, 780)
# 13:30 to 14:00  -> [810, 840)
donna_busy = [(540, 600), (630, 780), (810, 840)]
add_busy_constraints(solver, donna_busy)

# Bobby's busy intervals:
# 9:00 to 12:30   -> [540, 750)
# 13:00 to 15:00  -> [780, 900)
# 15:30 to 17:00  -> [930, 1020)
bobby_busy = [(540, 750), (780, 900), (930, 1020)]
add_busy_constraints(solver, bobby_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - 30 = 990.
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