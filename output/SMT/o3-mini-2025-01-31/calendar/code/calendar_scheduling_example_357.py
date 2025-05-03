from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function for busy constraints:
# For each busy interval [bs, be), the meeting must either end by bs or start after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Eric's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   11:30 to 12:00 -> [690, 720)
#   13:30 to 14:00 -> [810, 840)
#   16:30 to 17:00 -> [990, 1020)
eric_busy = [(570, 600), (690, 720), (810, 840), (990, 1020)]
add_busy_constraints(solver, eric_busy)

# Carol has no meetings, so no constraints to add.

# Nicholas's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   15:00 to 15:30 -> [900, 930)
nicholas_busy = [(690, 720), (900, 930)]
add_busy_constraints(solver, nicholas_busy)

# Randy's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   13:00 to 14:00 -> [780, 840)
#   15:00 to 16:00 -> [900, 960)
#   16:30 to 17:00 -> [990, 1020)
randy_busy = [(540, 570), (630, 690), (780, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, randy_busy)

# Kevin's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 13:00  -> [720, 780)
#   13:30 to 15:30  -> [810, 930)
#   16:00 to 16:30  -> [960, 990)
kevin_busy = [(540, 600), (660, 690), (720, 780), (810, 930), (960, 990)]
add_busy_constraints(solver, kevin_busy)

# Henry's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 12:00  -> [660, 720)
#   13:00 to 14:00  -> [780, 840)
#   15:30 to 16:30  -> [930, 990)
henry_busy = [(540, 600), (660, 720), (780, 840), (930, 990)]
add_busy_constraints(solver, henry_busy)

# Search for the earliest valid meeting start time that satisfies all constraints.
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