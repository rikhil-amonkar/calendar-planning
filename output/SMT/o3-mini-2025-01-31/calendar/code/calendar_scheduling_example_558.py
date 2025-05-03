from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Anthony doesn't want to meet before 14:00 (840 minutes),
# so we add the constraint that the meeting must start at or after 14:00.
solver.add(start >= 840)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure the meeting interval [start, start + duration)
    # does not overlap with the busy interval.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Douglas' busy intervals (in minutes):
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 15:00  -> [750, 900)
# 15:30 to 17:00  -> [930, 1020)
douglas_busy = [
    (540, 720),
    (750, 900),
    (930, 1020)
]
add_busy_constraints(solver, douglas_busy)

# Search for the earliest valid meeting time.
found = False
# To ensure the meeting ends by 17:00, the latest possible start time is 1020 - duration = 990.
for t in range(840, 991):
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