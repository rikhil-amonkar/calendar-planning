from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must fit completely within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must either finish before a busy interval
        # starts or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Samantha's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
samantha_busy = [(660, 690), (780, 810), (930, 960), (990, 1020)]
add_busy_constraints(solver, samantha_busy)

# Brian is free all day - no constraints needed.

# Arthur's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
arthur_busy = [(810, 840), (960, 990)]
add_busy_constraints(solver, arthur_busy)

# Matthew is free the entire day.

# Marilyn's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 13:00  -> [720, 780)
# 14:00 to 14:30  -> [840, 870)
# 16:00 to 16:30  -> [960, 990)
marilyn_busy = [(540, 600), (630, 690), (720, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, marilyn_busy)

# Mark's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 13:30  -> [690, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:00  -> [900, 960)
mark_busy = [(570, 660), (690, 810), (840, 870), (900, 960)]
add_busy_constraints(solver, mark_busy)

# Andrea's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 14:30  -> [690, 870)
# 15:00 to 15:30  -> [900, 930)
andrea_busy = [(570, 660), (690, 870), (900, 930)]
add_busy_constraints(solver, andrea_busy)

# Iterate over possible meeting start times (minute-by-minute) to find a valid slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()         # Save the current state
    solver.add(start == t)  # Try candidate start time
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes into HH:MM format
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()  # Restore state
        break
    solver.pop()      # Restore state if not sat

if not found:
    print("No valid meeting time could be found.")