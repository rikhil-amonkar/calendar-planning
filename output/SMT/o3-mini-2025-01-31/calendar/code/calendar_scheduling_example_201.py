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

# Helper function: For each busy interval [busy_start, busy_end),
# the meeting interval [start, start+duration) must either finish before busy_start
# or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Sara is free the whole day. (No busy intervals)

# Sarah's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 15:00 to 15:30 -> [900, 930)
sarah_busy = [(720, 750), (900, 930)]
add_busy_constraints(solver, sarah_busy)

# Shirley's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
shirley_busy = [(810, 840), (870, 900)]
add_busy_constraints(solver, shirley_busy)

# Harold's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:30 -> [630, 750)
# 13:00 to 17:00 -> [780, 1020)
harold_busy = [(540, 600), (630, 750), (780, 1020)]
add_busy_constraints(solver, harold_busy)

# Terry's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 17:00 -> [720, 1020)
terry_busy = [(540, 600), (630, 690), (720, 1020)]
add_busy_constraints(solver, terry_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991): 
    solver.push()  # Save state before trying a candidate time.
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
        solver.pop()  # Restore state.
        break
    solver.pop()  # Restore state if no solution for this candidate.

if not solution_found:
    print("No valid meeting time could be found.")