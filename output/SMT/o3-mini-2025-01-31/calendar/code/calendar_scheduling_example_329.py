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
        # Meeting avoids overlapping [bs, be) if it finishes before bs or starts after be.
        s.add(Or(start + duration <= bs, start >= be))

# Anna's blocked intervals:
#   11:00 to 11:30 → [660, 690)
#   16:00 to 16:30 → [960, 990)
anna_busy = [(660, 690), (960, 990)]
add_busy_constraints(solver, anna_busy)

# Samuel's blocked intervals:
#   9:00 to 9:30   → [540, 570)
#   15:30 to 16:00 → [930, 960)
samuel_busy = [(540, 570), (930, 960)]
add_busy_constraints(solver, samuel_busy)

# Joshua is free the entire day: no constraints needed.

# Eugene's meetings:
#   9:00 to 10:30  → [540, 630)
#   12:30 to 14:00 → [750, 840)
#   16:00 to 17:00 → [960, 1020)
eugene_busy = [(540, 630), (750, 840), (960, 1020)]
add_busy_constraints(solver, eugene_busy)

# Debra's meetings:
#   9:00 to 12:00  → [540, 720)
#   12:30 to 15:00 → [750, 900)
#   15:30 to 17:00 → [930, 1020)
debra_busy = [(540, 720), (750, 900), (930, 1020)]
add_busy_constraints(solver, debra_busy)

# Carolyn's meetings:
#   9:30 to 10:00   → [570, 600)
#   10:30 to 11:30  → [630, 690)
#   12:30 to 13:30  → [750, 810)
#   14:30 to 17:00  → [870, 1020)
carolyn_busy = [(570, 600), (630, 690), (750, 810), (870, 1020)]
add_busy_constraints(solver, carolyn_busy)

# Iterate to find the earliest valid meeting start time.
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