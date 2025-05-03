from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Virginia prefers to not have more meetings on Monday after 13:00.
# To respect this preference, we require the meeting to finish by 13:00 (780 minutes)
solver.add(start + duration <= 780)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start + duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Brandon's busy intervals (in minutes):
# 10:00 to 11:00   --> [600, 660)
# 12:30 to 13:00   --> [750, 780)
# 13:30 to 14:30   --> [810, 870)
# 15:00 to 15:30   --> [900, 930)
brandon_busy = [
    (600, 660),
    (750, 780),
    (810, 870),
    (900, 930)
]
add_busy_constraints(solver, brandon_busy)

# Virginia's busy intervals (in minutes):
# 9:00 to 10:30    --> [540, 630)
# 11:00 to 11:30   --> [660, 690)
# 12:30 to 13:00   --> [750, 780)
# 13:30 to 14:00   --> [810, 840)
# 14:30 to 16:30   --> [870, 990)
virginia_busy = [
    (540, 630),
    (660, 690),
    (750, 780),
    (810, 840),
    (870, 990)
]
add_busy_constraints(solver, virginia_busy)

# Search for the earliest valid meeting time.
found = False
# Since the meeting must finish by 13:00 (780 minutes), the latest possible start is 780 - 30 = 750.
for t in range(540, 751):
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