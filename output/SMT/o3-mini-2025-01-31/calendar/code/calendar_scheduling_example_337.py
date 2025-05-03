from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(sol, busy_intervals):
    # For each busy interval [bs, be), the meeting must either finish at or before bs 
    # or start at or after be.
    for bs, be in busy_intervals:
        sol.add(Or(start + duration <= bs, start >= be))

# John's busy intervals:
#   11:30 to 12:00 → [690, 720)
#   14:00 to 14:30 → [840, 870)
john_busy = [(690, 720), (840, 870)]
add_busy_constraints(solver, john_busy)

# Megan's busy intervals:
#   12:00 to 12:30 → [720, 750)
#   14:00 to 15:00 → [840, 900)
#   15:30 to 16:00 → [930, 960)
megan_busy = [(720, 750), (840, 900), (930, 960)]
add_busy_constraints(solver, megan_busy)

# Brandon has no meetings, so no constraints are added.

# Kimberly's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 10:30 → [600, 630)
#   11:00 to 14:30 → [660, 870)
#   15:00 to 16:00 → [900, 960)
#   16:30 to 17:00 → [990, 1020)
kimberly_busy = [(540, 570), (600, 630), (660, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, kimberly_busy)

# Sean's busy intervals:
#   10:00 to 11:00 → [600, 660)
#   11:30 to 14:00 → [690, 840)
#   15:00 to 15:30 → [900, 930)
sean_busy = [(600, 660), (690, 840), (900, 930)]
add_busy_constraints(solver, sean_busy)

# Lori's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:30 to 12:00 → [630, 720)
#   13:00 to 14:30 → [780, 870)
#   16:00 to 16:30 → [960, 990)
lori_busy = [(540, 570), (630, 720), (780, 870), (960, 990)]
add_busy_constraints(solver, lori_busy)

# Find the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state before breaking
        break
    solver.pop()  # Restore state and try next minute

if not found:
    print("No valid meeting time could be found.")