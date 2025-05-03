from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure that the meeting does not overlap with a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting can avoid a busy interval if it finishes on or before the interval starts
        # or starts on or after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Shirley's busy interval:
#   11:00 to 12:00 -> [660, 720)
shirley_busy = [(660, 720)]
add_busy_constraints(solver, shirley_busy)

# Carl has no meetings: no busy intervals.

# Bradley has no meetings: no busy intervals.

# Kevin's busy intervals:
#   9:00 to 12:30  -> [540, 750)
#   13:00 to 16:00 -> [780, 960)
#   16:30 to 17:00 -> [990, 1020)
kevin_busy = [(540, 750), (780, 960), (990, 1020)]
add_busy_constraints(solver, kevin_busy)

# Walter's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 12:00 -> [660, 720)
#   12:30 to 13:00 -> [750, 780)
#   14:30 to 15:30 -> [870, 930)
#   16:30 to 17:00 -> [990, 1020)
walter_busy = [(540, 570), (600, 630), (660, 720), (750, 780), (870, 930), (990, 1020)]
add_busy_constraints(solver, walter_busy)

# Anna's busy intervals:
#   9:00 to 10:00  -> [540, 600)
#   11:00 to 13:00 -> [660, 780)
#   14:00 to 15:00 -> [840, 900)
anna_busy = [(540, 600), (660, 780), (840, 900)]
add_busy_constraints(solver, anna_busy)

# Search for the earliest valid meeting start time by checking every minute from 9:00 until the meeting can finish by 17:00.
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