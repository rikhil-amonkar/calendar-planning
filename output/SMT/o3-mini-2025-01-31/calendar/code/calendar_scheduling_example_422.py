from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Julie's busy intervals:
# 9:00 to 10:00   => [540, 600)
# 12:00 to 12:30  => [720, 750)
# 13:00 to 13:30  => [780, 810)
# 14:00 to 15:00  => [840, 900)
julie_busy = [(540, 600), (720, 750), (780, 810), (840, 900)]
add_busy_constraints(solver, julie_busy)

# Ann's busy intervals:
# 10:30 to 11:00  => [630, 660)
# 14:30 to 15:00  => [870, 900)
ann_busy = [(630, 660), (870, 900)]
add_busy_constraints(solver, ann_busy)

# Kenneth has no meetings (no constraints).

# Austin is free the entire day (no constraints).

# Edward's busy intervals:
# 9:00 to 9:30    => [540, 570)
# 10:00 to 12:30  => [600, 750)
# 13:00 to 13:30  => [780, 810)
# 15:00 to 15:30  => [900, 930)
# 16:00 to 17:00  => [960, 1020)
edward_busy = [(540, 570), (600, 750), (780, 810), (900, 930), (960, 1020)]
add_busy_constraints(solver, edward_busy)

# Christine's busy intervals:
# 9:00 to 15:30   => [540, 930)
# 16:30 to 17:00  => [990, 1020)
christine_busy = [(540, 930), (990, 1020)]
add_busy_constraints(solver, christine_busy)

# Carol's busy intervals:
# 9:00 to 10:00    => [540, 600)
# 10:30 to 13:00   => [630, 780)
# 13:30 to 15:30   => [810, 930)
# 16:00 to 16:30   => [960, 990)
carol_busy = [(540, 600), (630, 780), (810, 930), (960, 990)]
add_busy_constraints(solver, carol_busy)

# Iterate over possible start times to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
              start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")