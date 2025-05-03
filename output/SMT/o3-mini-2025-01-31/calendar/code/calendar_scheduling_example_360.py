from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))
        
# Emily's busy intervals:
#  10:00 to 10:30 -> [600, 630)
#  16:00 to 16:30 -> [960, 990)
emily_busy = [(600, 630), (960, 990)]
add_busy_constraints(solver, emily_busy)

# Mason is free all day (no busy intervals)

# Maria's busy intervals:
#  10:30 to 11:00 -> [630, 660)
#  14:00 to 14:30 -> [840, 870)
maria_busy = [(630, 660), (840, 870)]
add_busy_constraints(solver, maria_busy)

# Carl's busy intervals:
#  9:30 to 10:00   -> [570, 600)
#  10:30 to 12:30  -> [630, 750)
#  13:30 to 14:00  -> [810, 840)
#  14:30 to 15:30  -> [870, 930)
#  16:00 to 17:00  -> [960, 1020)
carl_busy = [(570, 600), (630, 750), (810, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, carl_busy)

# David's busy intervals:
#  9:30 to 11:00   -> [570, 660)
#  11:30 to 12:00  -> [690, 720)
#  12:30 to 13:30  -> [750, 810)
#  14:00 to 15:00  -> [840, 900)
#  16:00 to 17:00  -> [960, 1020)
david_busy = [(570, 660), (690, 720), (750, 810), (840, 900), (960, 1020)]
add_busy_constraints(solver, david_busy)

# Frank's busy intervals:
#  9:30 to 10:30  -> [570, 630)
#  11:00 to 11:30 -> [660, 690)
#  12:30 to 13:30 -> [750, 810)
#  14:30 to 17:00 -> [870, 1020)
frank_busy = [(570, 630), (660, 690), (750, 810), (870, 1020)]
add_busy_constraints(solver, frank_busy)

# Now, iterate over all possible start times in the workday to find the earliest meeting time.
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