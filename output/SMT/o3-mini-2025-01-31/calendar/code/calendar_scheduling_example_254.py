from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Cheryl, Judith, and Ann are free the entire day so no busy constraints are needed for them.

# Joseph's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
joseph_busy = [(540, 630), (660, 690), (780, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, joseph_busy)

# Douglas's busy intervals:
# 9:00 to 12:30  -> [540, 750)
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 17:00 -> [900, 1020)
douglas_busy = [(540, 750), (780, 870), (900, 1020)]
add_busy_constraints(solver, douglas_busy)

# Find an earliest valid meeting time by iterating over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")