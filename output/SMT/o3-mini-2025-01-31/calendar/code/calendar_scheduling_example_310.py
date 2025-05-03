from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting and busy interval do not overlap if:
        # either the meeting ends on or before the busy interval begins,
        # or the meeting starts on or after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Helen's busy intervals:
#   12:00 to 12:30 -> [720, 750)
#   15:30 to 16:00 -> [930, 960)
helen_busy = [(720, 750), (930, 960)]
add_busy_constraints(solver, helen_busy)

# Sophia's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 16:00 -> [900, 960)
sophia_busy = [(690, 720), (780, 810), (900, 960)]
add_busy_constraints(solver, sophia_busy)

# Anthony's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 12:30 -> [720, 750)
#   15:30 to 16:30 -> [930, 990)
anthony_busy = [(540, 570), (630, 690), (720, 750), (930, 990)]
add_busy_constraints(solver, anthony_busy)

# Hannah's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   12:00 to 13:30  -> [720, 810)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 17:00  -> [900, 1020)
hannah_busy = [(540, 660), (720, 810), (840, 870), (900, 1020)]
add_busy_constraints(solver, hannah_busy)

# Donna's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 13:00 -> [660, 780)
#   15:00 to 17:00 -> [900, 1020)
donna_busy = [(540, 570), (600, 630), (660, 780), (900, 1020)]
add_busy_constraints(solver, donna_busy)

# Brittany's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   10:30 to 12:30 -> [630, 750)
#   13:00 to 14:00 -> [780, 840)
#   15:30 to 16:00 -> [930, 960)
brittany_busy = [(570, 600), (630, 750), (780, 840), (930, 960)]
add_busy_constraints(solver, brittany_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # t ranges from 540 to 990 (inclusive)
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