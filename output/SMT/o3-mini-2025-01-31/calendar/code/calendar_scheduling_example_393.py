from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 (540) to 17:00 (1020)
# and meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Samantha is free the entire day, so no constraints.

# Nancy's busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   11:00 to 11:30 -> [660, 690)
nancy_busy = [(540, 570), (660, 690)]
add_busy_constraints(solver, nancy_busy)

# Steven is free the entire day, so no constraints.

# William's busy intervals:
#   11:00 to 12:00 -> [660, 720)
#   13:00 to 13:30 -> [780, 810)
#   14:00 to 16:30 -> [840, 990)
william_busy = [(660, 720), (780, 810), (840, 990)]
add_busy_constraints(solver, william_busy)

# Karen's busy intervals:
#   9:00 to 12:00   -> [540, 720)
#   12:30 to 13:00  -> [750, 780)
#   13:30 to 17:00  -> [810, 1020)
karen_busy = [(540, 720), (750, 780), (810, 1020)]
add_busy_constraints(solver, karen_busy)

# Tyler's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   13:30 to 15:00  -> [810, 900)
#   15:30 to 17:00  -> [930, 1020)
tyler_busy = [(540, 660), (690, 720), (750, 780), (810, 900), (930, 1020)]
add_busy_constraints(solver, tyler_busy)

# Find the earliest meeting time by iterating minute-by-minute.
found = False
for t in range(540, 1020 - duration + 1):
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