from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is one hour (60 minutes)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Define a helper function to ensure that the meeting interval does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start + duration) must not overlap with [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Evelyn has a free day, so no busy intervals to add for her.

# Jason's busy intervals (in minutes):
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:30  -> [600, 690)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 17:00  -> [900, 1020)
jason_busy = [
    (540, 570),
    (600, 690),
    (750, 870),
    (900, 1020)
]
add_busy_constraints(solver, jason_busy)

# Now, search for the earliest valid one-hour meeting time.
found = False
# The latest possible start is 1020 - 60 = 960, so we'll iterate over the range [540, 960]
for t in range(540, 960 + 1):
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