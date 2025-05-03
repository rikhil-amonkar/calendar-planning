from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Wayne prefers to avoid meetings before 14:00 (840 minutes).
# We add this as a hard constraint.
solver.add(start >= 840)

# Helper function to add non-overlap constraints for a list of busy intervals.
# Each busy interval is given as (busy_start, busy_end) in minutes.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before the busy interval starts, or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Melissa's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:30 to 14:00 -> [750, 840)
# 15:00 to 15:30 -> [900, 930)
melissa_busy = [(600, 660), (750, 840), (900, 930)]
add_busy_constraints(solver, melissa_busy)

# Catherine is free the entire day, so no constraints needed.

# Gregory's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:00 -> [930, 960)
gregory_busy = [(750, 780), (930, 960)]
add_busy_constraints(solver, gregory_busy)

# Victoria's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:30 -> [930, 990)
victoria_busy = [(540, 570), (630, 690), (780, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, victoria_busy)

# Thomas's busy intervals:
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 16:00 -> [870, 960)
thomas_busy = [(600, 720), (750, 780), (870, 960)]
add_busy_constraints(solver, thomas_busy)

# Jennifer's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 13:00 -> [660, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
jennifer_busy = [(540, 570), (600, 630), (660, 780), (810, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, jennifer_busy)

# Wayne is free, so no busy intervals for him.

# Try possible meeting start times (remember, Wayne prefers after 14:00 so start>=840).
found = False
for t in range(840, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")