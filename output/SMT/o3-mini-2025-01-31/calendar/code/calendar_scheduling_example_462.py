from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper to add non-overlap constraints for busy intervals.
# Each busy interval is represented as (busy_start, busy_end) in minutes.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before 
        # the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Terry's calendar is wide open (no constraints).

# Justin's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
justin_busy = [(690, 720), (780, 810)]
add_busy_constraints(solver, justin_busy)

# Grace is free the entire day (no constraints).

# Bruce's calendar is wide open (no constraints).

# Diane's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 16:30 -> [960, 990)
diane_busy = [(570, 630), (690, 720), (750, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, diane_busy)

# Bryan's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
bryan_busy = [(540, 630), (720, 750), (780, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, bryan_busy)

# Beverly's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 17:00 -> [960, 1020)
beverly_busy = [(570, 630), (690, 750), (780, 810), (840, 870), (960, 1020)]
add_busy_constraints(solver, beverly_busy)

# To honor the group's preference for the earliest availability,
# we iterate over possible start times in increasing order.
found = False
for t in range(540, 1020 - duration + 1):
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