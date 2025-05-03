from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes from midnight

# Constrain the meeting time to be within work hours
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting doesn't overlap a busy interval if it ends on or before it starts,
        # or begins on or after it ends.
        s.add( Or(start + duration <= bs, start >= be) )

# Brittany's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   10:30 to 11:00 -> [630, 660)
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 13:30 -> [780, 810)
#   16:00 to 17:00 -> [960, 1020)
brittany_busy = [(570, 600), (630, 660), (690, 720), (780, 810), (960, 1020)]
add_busy_constraints(solver, brittany_busy)

# Gloria's busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 15:30 -> [900, 930)
gloria_busy = [(540, 570), (600, 630), (780, 810), (900, 930)]
add_busy_constraints(solver, gloria_busy)

# Lisa's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:00 -> [810, 840)
lisa_busy = [(750, 780), (810, 840)]
add_busy_constraints(solver, lisa_busy)

# Paul's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 13:00 -> [660, 780)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
paul_busy = [(540, 570), (660, 780), (810, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, paul_busy)

# Justin's busy intervals:
#   9:30 to 13:00  -> [570, 780)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 17:00 -> [900, 1020)
justin_busy = [(570, 780), (810, 840), (900, 1020)]
add_busy_constraints(solver, justin_busy)

# Diana's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 13:30 -> [720, 810)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
diana_busy = [(540, 630), (660, 690), (720, 810), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, diana_busy)

# Search for the earliest valid meeting start time.
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