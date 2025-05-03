from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting is non-overlapping with a busy interval if it ends 
        # on or before the interval starts, or starts on or after the interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Kathryn is free, so no busy intervals.

# Janet's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:00 -> [930, 960)
janet_busy = [(630, 660), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, janet_busy)

# Alexander's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   11:30 to 12:00  -> [690, 720)
#   14:30 to 15:00  -> [870, 900)
#   16:30 to 17:00  -> [990, 1020)
alexander_busy = [(570, 600), (690, 720), (870, 900), (990, 1020)]
add_busy_constraints(solver, alexander_busy)

# Alan's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   13:00 to 14:00  -> [780, 840)
#   15:00 to 15:30  -> [900, 930)
#   16:30 to 17:00  -> [990, 1020)
alan_busy = [(540, 660), (780, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, alan_busy)

# Henry's busy intervals:
#   9:00 to 13:30   -> [540, 810)
#   14:30 to 17:00  -> [870, 1020)
henry_busy = [(540, 810), (870, 1020)]
add_busy_constraints(solver, henry_busy)

# Search for a valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # iterate through possible start times
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