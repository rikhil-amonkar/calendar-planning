from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 60  # meeting duration in minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Jean's busy intervals (in minutes):
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 12:30 to 13:30 -> [750, 810)
jean_busy = [
    (570, 600),
    (630, 660),
    (750, 810)
]
add_busy_constraints(solver, jean_busy)

# Amanda's busy intervals (in minutes):
# 9:00 to 10:30  -> [540, 630)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:30 to 17:00 -> [930, 1020)
amanda_busy = [
    (540, 630),
    (690, 750),
    (780, 840),
    (930, 1020)
]
add_busy_constraints(solver, amanda_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - duration = 1020 - 60 = 960.
for t in range(540, 961):
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