from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration: half an hour
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540) and 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Bobby would rather not meet before 13:00 (780 minutes),
# so force the meeting to start at or after 13:00.
solver.add(start >= 780)

# Helper function to add busy time constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Bobby's busy intervals (in minutes since midnight):
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 14:30 to 15:00  -> [870, 900)
bobby_busy = [
    (540, 600),
    (630, 720),
    (870, 900)
]
add_busy_constraints(solver, bobby_busy)

# Doris's busy intervals (in minutes since midnight):
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 13:30  -> [780, 810)
# 15:00 to 17:00  -> [900, 1020)
doris_busy = [
    (630, 660),
    (690, 750),
    (780, 810),
    (900, 1020)
]
add_busy_constraints(solver, doris_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest start is 1020 - duration = 990.
for t in range(780, 991):  # starting from 13:00 (780) per Bobby's preference
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