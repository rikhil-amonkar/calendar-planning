from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Kayla prefers not to meet before 11:00 (660 minutes).
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours and respect Kayla's preference.
solver.add(start >= 660, start + duration <= 1020)

# Helper function: for each busy interval [bs, be),
# the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Peter's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 13:30 -> [780, 810)
#   15:30 to 16:00 -> [930, 960)
peter_busy = [(630, 660), (690, 720), (780, 810), (930, 960)]
add_busy_constraints(solver, peter_busy)

# Grace's busy intervals:
#   11:30 to 13:00 -> [690, 780)
#   15:00 to 15:30 -> [900, 930)
grace_busy = [(690, 780), (900, 930)]
add_busy_constraints(solver, grace_busy)

# Julie's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:00  -> [630, 660)
#   14:00 to 15:00  -> [840, 900)
#   15:30 to 16:30  -> [930, 990)
julie_busy = [(570, 600), (630, 660), (840, 900), (930, 990)]
add_busy_constraints(solver, julie_busy)

# Kayla's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 14:30 -> [750, 870)
#   15:00 to 16:00 -> [900, 960)
#   16:30 to 17:00 -> [990, 1020)
kayla_busy = [(690, 720), (750, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, kayla_busy)

# Emma's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 15:30 -> [780, 930)
emma_busy = [(540, 570), (630, 660), (690, 720), (780, 930)]
add_busy_constraints(solver, emma_busy)

# Scott's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 14:00  -> [780, 840)
#   14:30 to 15:30  -> [870, 930)
#   16:00 to 16:30  -> [960, 990)
scott_busy = [(540, 600), (720, 750), (780, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, scott_busy)

# Iterate over each possible start minute (from 660 to 1020 - duration) to find a valid meeting time.
found = False
for t in range(660, 1020 - duration + 1):
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