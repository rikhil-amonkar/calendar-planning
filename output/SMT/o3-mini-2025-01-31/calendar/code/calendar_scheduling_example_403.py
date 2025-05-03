from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to avoid overlapping busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting must finish before a busy interval starts OR start after a busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Wayne's busy intervals:
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
wayne_busy = [(870, 900), (930, 960)]
add_busy_constraints(solver, wayne_busy)

# Edward, Lauren, Helen are free the entire day, so no constraints for them.

# Michael's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:30  -> [810, 870)
# 16:00 to 17:00  -> [960, 1020)
michael_busy = [(540, 600), (630, 690), (720, 780), (810, 870), (960, 1020)]
add_busy_constraints(solver, michael_busy)

# Joseph's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:00  -> [930, 960)
joseph_busy = [(540, 720), (840, 870), (930, 960)]
add_busy_constraints(solver, joseph_busy)

# Vincent's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 17:00  -> [870, 1020)
vincent_busy = [(540, 630), (690, 780), (810, 840), (870, 1020)]
add_busy_constraints(solver, vincent_busy)

# Iterate over possible start times (minute-by-minute) to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()         # Save the state
    solver.add(start == t)  # Try candidate start time
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()      # Restore state
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")