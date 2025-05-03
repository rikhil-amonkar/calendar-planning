from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# But Kayla does not want to meet before 10:30 (630 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours and respect Kayla's preference.
solver.add(start >= 630, start + duration <= 1020)

# Helper function: for each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))
        
# Charles: No meetings throughout the day, so no constraints.

# Kayla's busy intervals:
#   12:00 to 13:00 -> [720, 780)
kayla_busy = [(720, 780)]
add_busy_constraints(solver, kayla_busy)

# Cynthia: free all day, so no constraints.

# Rebecca's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   12:00 to 14:00 -> [720, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
rebecca_busy = [(600, 630), (720, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, rebecca_busy)

# Randy's busy intervals:
#   10:00 to 11:30 -> [600, 690)
#   12:00 to 13:30 -> [720, 810)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 17:00 -> [960, 1020)
randy_busy = [(600, 690), (720, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, randy_busy)

# Hannah's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 12:00 -> [600, 720)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 15:30 -> [870, 930)
#   16:30 to 17:00 -> [990, 1020)
hannah_busy = [(540, 570), (600, 720), (750, 780), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, hannah_busy)

# Iterate over each possible start minute (from 630 to 1020 - duration) to find a valid meeting time.
found = False
for t in range(630, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")