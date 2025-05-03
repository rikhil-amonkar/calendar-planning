from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(s, busy_intervals):
    for (bs, be) in busy_intervals:
        # The meeting avoids overlapping with [bs, be) if either:
        # it ends before bs or it starts after be.
        s.add(Or(start + duration <= bs, start >= be))

# Cynthia's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 12:30 -> [720, 750)
#   14:00 to 16:00 -> [840, 960)
cynthia_busy = [(660, 690), (720, 750), (840, 960)]
add_busy_constraints(solver, cynthia_busy)

# Megan's busy intervals:
#   10:00 to 11:30 -> [600, 690)
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 14:30 -> [840, 870)
#   15:30 to 16:00 -> [930, 960)
megan_busy = [(600, 690), (750, 780), (840, 870), (930, 960)]
add_busy_constraints(solver, megan_busy)

# Christopher has no meetings, so no constraints are needed for him.

# Philip's busy intervals:
#   9:00 to 11:30  -> [540, 690)
#   12:00 to 13:00 -> [720, 780)
#   13:30 to 17:00 -> [810, 1020)
philip_busy = [(540, 690), (720, 780), (810, 1020)]
add_busy_constraints(solver, philip_busy)

# Ryan's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:00 to 11:30  -> [660, 690)
#   12:30 to 15:30  -> [750, 930)
#   16:00 to 17:00  -> [960, 1020)
ryan_busy = [(540, 630), (660, 690), (750, 930), (960, 1020)]
add_busy_constraints(solver, ryan_busy)

# Lauren's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 13:00  -> [720, 780)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 17:00  -> [900, 1020)
lauren_busy = [(570, 630), (660, 690), (720, 780), (840, 870), (900, 1020)]
add_busy_constraints(solver, lauren_busy)

# Attempt to find the earliest valid meeting start time.
found = False
# Iterate possible start times from 9:00 (540) to latest possible such that meeting ends by 17:00.
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