from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), ensure the meeting either ends by bs or starts at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Virginia: free all day, no constraints.

# Janet's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 15:30 -> [810, 930)
janet_busy = [(570, 600), (750, 780), (810, 930)]
add_busy_constraints(solver, janet_busy)

# Joyce's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   15:30 to 17:00 -> [930, 1020)
joyce_busy = [(750, 780), (930, 1020)]
add_busy_constraints(solver, joyce_busy)

# Catherine's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 16:30  -> [630, 990)
catherine_busy = [(540, 600), (630, 990)]
add_busy_constraints(solver, catherine_busy)

# Donna's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 11:30 -> [660, 690)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 17:00 -> [870, 1020)
donna_busy = [(540, 570), (660, 690), (780, 810), (870, 1020)]
add_busy_constraints(solver, donna_busy)

# Evelyn's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   12:00 to 15:30 -> [720, 930)
#   16:00 to 17:00 -> [960, 1020)
evelyn_busy = [(630, 660), (720, 930), (960, 1020)]
add_busy_constraints(solver, evelyn_busy)

# Now, iterate over possible start times within the allowed hours to find a valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")