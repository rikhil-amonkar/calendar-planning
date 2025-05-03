from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(s, busy_intervals):
    for (bs, be) in busy_intervals:
        # The meeting avoids overlapping with [bs, be) if it either finishes
        # on or before bs, or starts on or after be.
        s.add(Or(start + duration <= bs, start >= be))

# Diana's meetings:
#   13:30 to 14:00 → [810, 840)
#   16:30 to 17:00 → [990, 1020)
diana_busy = [(810, 840), (990, 1020)]
add_busy_constraints(solver, diana_busy)

# Timothy's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   12:00 to 12:30 → [720, 750)
#   13:00 to 13:30 → [780, 810)
#   14:00 to 14:30 → [840, 870)
timothy_busy = [(540, 570), (720, 750), (780, 810), (840, 870)]
add_busy_constraints(solver, timothy_busy)

# Patrick's busy intervals:
#   9:00 to 9:30    → [540, 570)
#   10:30 to 11:00  → [630, 660)
#   11:30 to 12:30  → [690, 750)
#   14:30 to 15:00  → [870, 900)
#   16:00 to 16:30  → [960, 990)
patrick_busy = [(540, 570), (630, 660), (690, 750), (870, 900), (960, 990)]
add_busy_constraints(solver, patrick_busy)

# Janet's meetings:
#   9:30 to 10:30   → [570, 630)
#   11:00 to 12:00  → [660, 720)
#   13:00 to 13:30  → [780, 810)
#   14:00 to 16:30  → [840, 990)
janet_busy = [(570, 630), (660, 720), (780, 810), (840, 990)]
add_busy_constraints(solver, janet_busy)

# Megan's meetings:
#   9:00 to 12:30   → [540, 750)
#   13:00 to 13:30  → [780, 810)
#   14:00 to 17:00  → [840, 1020)
megan_busy = [(540, 750), (780, 810), (840, 1020)]
add_busy_constraints(solver, megan_busy)

# Evelyn's calendar blocks:
#   9:00 to 10:30   → [540, 630)
#   11:00 to 12:30  → [660, 750)
#   13:00 to 17:00  → [780, 1020)
evelyn_busy = [(540, 630), (660, 750), (780, 1020)]
add_busy_constraints(solver, evelyn_busy)

# Search for the earliest valid meeting start time.
found = False
# The meeting can start any time t such that 540 <= t <= 1020 - duration.
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