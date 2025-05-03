from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must end before bs or start after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Noah's busy intervals:
#   11:00 to 12:00  -> [660, 720)
#   12:30 to 13:00  -> [750, 780)
#   14:30 to 15:30  -> [870, 930)
#   16:30 to 17:00  -> [990, 1020)
noah_busy = [(660, 720), (750, 780), (870, 930), (990, 1020)]
add_busy_constraints(solver, noah_busy)

# Ralph's busy intervals:
#   10:30 to 11:00  -> [630, 660)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 14:00  -> [780, 840)
#   14:30 to 15:00  -> [870, 900)
#   16:30 to 17:00  -> [990, 1020)
ralph_busy = [(630, 660), (720, 750), (780, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, ralph_busy)

# Sean's busy intervals:
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 15:30  -> [870, 930)
#   16:30 to 17:00  -> [990, 1020)
sean_busy = [(780, 810), (870, 930), (990, 1020)]
add_busy_constraints(solver, sean_busy)

# John's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 11:30  -> [660, 690)
#   13:00 to 16:00  -> [780, 960)
#   16:30 to 17:00  -> [990, 1020)
john_busy = [(570, 630), (660, 690), (780, 960), (990, 1020)]
add_busy_constraints(solver, john_busy)

# Harold's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   11:30 to 12:30  -> [690, 750)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 15:30  -> [840, 930)
#   16:30 to 17:00  -> [990, 1020)
harold_busy = [(570, 600), (690, 750), (780, 810), (840, 930), (990, 1020)]
add_busy_constraints(solver, harold_busy)

# Austin's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   11:30 to 14:00  -> [690, 840)
#   14:30 to 17:00  -> [870, 1020)
austin_busy = [(600, 660), (690, 840), (870, 1020)]
add_busy_constraints(solver, austin_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore before breaking
        break
    solver.pop()  # Restore state and try the next candidate

if not found:
    print("No valid meeting time could be found.")