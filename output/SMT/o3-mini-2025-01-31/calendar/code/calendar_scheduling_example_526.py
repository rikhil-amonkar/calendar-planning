from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint:
# Nicholas would rather not meet on Monday after 14:30.
# Thus, the meeting must finish no later than 14:30 (870 minutes).
solver.add(start + duration <= 870)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Harold's busy intervals (in minutes):
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 13:00 to 13:30  -> [780, 810)
# 15:30 to 16:00  -> [930, 960)
harold_busy = [
    (570, 600),
    (630, 660),
    (780, 810),
    (930, 960)
]
add_busy_constraints(solver, harold_busy)

# Nicholas's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 17:00  -> [900, 1020)
nicholas_busy = [
    (540, 600),
    (630, 720),
    (750, 810),
    (840, 870),
    (900, 1020)
]
add_busy_constraints(solver, nicholas_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 870, so the latest possible start time is 870 - duration = 840.
for t in range(540, 841):
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