from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Susan's calendar is completely free,
# so there are no additional busy constraints for Susan.

# Diane's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 12:00 to 14:00  -> [720, 840)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
diane_busy = [
    (540, 600),
    (720, 840),
    (900, 930),
    (990, 1020)
]

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with
        # any busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

add_busy_constraints(solver, diane_busy)

# We want to find the earliest available time slot.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")