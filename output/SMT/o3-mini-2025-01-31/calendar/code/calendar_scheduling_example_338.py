from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlapping constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    # Each busy interval is represented as [bs, be)
    # The meeting must either end before a busy interval starts, or start after it ends.
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Alexander's busy intervals:
#   12:00 to 12:30 → [720, 750)
#   14:30 to 16:00 → [870, 960)
alex_busy = [(720, 750), (870, 960)]
add_busy_constraints(solver, alex_busy)

# Amy's busy intervals:
#   10:00 to 10:30 → [600, 630)
#   12:00 to 12:30 → [720, 750)
#   15:30 to 16:00 → [930, 960)
#   16:30 to 17:00 → [990, 1020)
amy_busy = [(600, 630), (720, 750), (930, 960), (990, 1020)]
add_busy_constraints(solver, amy_busy)

# Christopher's busy intervals:
#   10:30 to 11:30 → [630, 690)
chris_busy = [(630, 690)]
add_busy_constraints(solver, chris_busy)

# Kyle's busy intervals:
#   9:30 to 10:00   → [570, 600)
#   11:30 to 12:30  → [690, 750)
#   13:00 to 14:00  → [780, 840)
#   14:30 to 15:30  → [870, 930)
#   16:00 to 16:30  → [960, 990)
kyle_busy = [(570, 600), (690, 750), (780, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, kyle_busy)

# Jerry's busy intervals:
#   9:30 to 11:30  → [570, 690)
#   12:00 to 12:30 → [720, 750)
#   13:30 to 14:00 → [810, 840)
#   15:00 to 16:00 → [900, 960)
jerry_busy = [(570, 690), (720, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, jerry_busy)

# Raymond's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 10:30 → [600, 630)
#   11:00 to 12:30 → [660, 750)
#   13:00 to 15:30 → [780, 930)
#   16:00 to 17:00 → [960, 1020)
raymond_busy = [(540, 570), (600, 630), (660, 750), (780, 930), (960, 1020)]
add_busy_constraints(solver, raymond_busy)

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
        solver.pop()  # Restore solver state before exiting loop
        break
    solver.pop()  # Restore state and try the next time slot

if not found:
    print("No valid meeting time could be found.")