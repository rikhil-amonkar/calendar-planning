from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(s, busy_intervals):
    # For each busy interval [bs, be), the meeting must either end before bs or start at/after be.
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Cheryl's busy intervals:
#   12:30 to 13:00 → [750, 780)
#   16:30 to 17:00 → [990, 1020)
cheryl_busy = [(750, 780), (990, 1020)]
add_busy_constraints(solver, cheryl_busy)

# Bryan's busy intervals:
#   11:30 to 12:30 → [690, 750)
#   16:00 to 17:00 → [960, 1020)
bryan_busy = [(690, 750), (960, 1020)]
add_busy_constraints(solver, bryan_busy)

# Joseph's calendar is wide open the entire day, so no constraints.

# Maria's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 11:30 → [600, 690)
#   12:00 to 12:30 → [720, 750)
#   14:00 to 14:30 → [840, 870)
#   15:00 to 15:30 → [900, 930)
#   16:00 to 16:30 → [960, 990)
maria_busy = [(540, 570), (600, 690), (720, 750), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, maria_busy)

# Elizabeth's busy intervals:
#   9:00 to 10:00   → [540, 600)
#   10:30 to 11:00  → [630, 660)
#   12:30 to 13:30  → [750, 810)
#   15:00 to 16:00  → [900, 960)
#   16:30 to 17:00  → [990, 1020)
elizabeth_busy = [(540, 600), (630, 660), (750, 810), (900, 960), (990, 1020)]
add_busy_constraints(solver, elizabeth_busy)

# Kimberly's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 10:30 → [600, 630)
#   11:00 to 12:00 → [660, 720)
#   12:30 to 13:00 → [750, 780)
#   13:30 to 14:00 → [810, 840)
#   16:00 to 17:00 → [960, 1020)
kimberly_busy = [(540, 570), (600, 630), (660, 720), (750, 780), (810, 840), (960, 1020)]
add_busy_constraints(solver, kimberly_busy)

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
        solver.pop()  # Restore state before exiting the loop
        break
    solver.pop()  # Restore and try the next time slot

if not found:
    print("No valid meeting time could be found.")