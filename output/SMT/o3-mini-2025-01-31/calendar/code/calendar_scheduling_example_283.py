from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must end on or before a busy interval starts, or start on or after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Juan's calendar is wide open, no busy intervals.

# Rachel's busy intervals:
#   12:00 to 12:30 -> [720, 750)
#   15:00 to 15:30 -> [900, 930)
rachel_busy = [(720, 750), (900, 930)]
add_busy_constraints(solver, rachel_busy)

# Alexander's busy intervals:
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
alexander_busy = [(840, 870), (900, 930)]
add_busy_constraints(solver, alexander_busy)

# Aaron's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:30 to 17:00 -> [690, 1020)
aaron_busy = [(540, 630), (690, 1020)]
add_busy_constraints(solver, aaron_busy)

# Hannah's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 14:30 -> [750, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 16:30 -> [960, 990)
hannah_busy = [(540, 570), (660, 690), (750, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, hannah_busy)

# Search for a valid meeting time. We try every minute from 9:00 (540) 
# up to the last possible start time that fits a 30-minute meeting.
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