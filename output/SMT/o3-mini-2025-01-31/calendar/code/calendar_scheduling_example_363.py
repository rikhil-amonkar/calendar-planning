from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Peter: free all day (no busy intervals)

# Amber: free all day (no busy intervals)

# Russell's busy intervals:
#  14:30 to 15:00 -> [870, 900)
#  15:30 to 17:00 -> [930, 1020)
russell_busy = [(870, 900), (930, 1020)]
add_busy_constraints(solver, russell_busy)

# Paul's busy intervals:
#  9:00 to 10:00   -> [540, 600)
#  10:30 to 12:30  -> [630, 750)
#  13:00 to 15:00  -> [780, 900)
#  15:30 to 16:00  -> [930, 960)
#  16:30 to 17:00  -> [990, 1020)
paul_busy = [(540, 600), (630, 750), (780, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, paul_busy)

# Donna's busy intervals:
#  9:00 to 9:30   -> [540, 570)
#  10:00 to 11:00  -> [600, 660)
#  11:30 to 12:30  -> [690, 750)
#  14:00 to 14:30  -> [840, 870)
#  15:00 to 15:30  -> [900, 930)
#  16:00 to 16:30  -> [960, 990)
donna_busy = [(540, 570), (600, 660), (690, 750), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, donna_busy)

# Isabella's busy intervals:
#  9:30 to 10:00   -> [570, 600)
#  11:00 to 11:30  -> [660, 690)
#  12:00 to 12:30  -> [720, 750)
#  13:00 to 13:30  -> [780, 810)
#  14:00 to 14:30  -> [840, 870)
#  15:00 to 15:30  -> [900, 930)
#  16:00 to 17:00  -> [960, 1020)
isabella_busy = [(570, 600), (660, 690), (720, 750), (780, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, isabella_busy)

# Iterate over possible start times within work hours to find a valid meeting time.
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