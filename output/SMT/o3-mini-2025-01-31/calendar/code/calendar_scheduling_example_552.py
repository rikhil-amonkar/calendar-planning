from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Margaret's constraint: Cannot meet on Monday after 14:00.
# We interpret this as the meeting must finish by 14:00 (840 minutes).
solver.add(start + duration <= 840)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Brian has no meetings, so no busy intervals.
brian_busy = []
add_busy_constraints(solver, brian_busy)

# Margaret's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 14:30 -> [720, 870)
# 15:30 to 17:00 -> [930, 1020)
margaret_busy = [
    (540, 570),
    (600, 630),
    (720, 870),
    (930, 1020)
]
add_busy_constraints(solver, margaret_busy)

# Search for the earliest valid meeting time.
found = False
# Because Margaret requires the meeting to finish by 14:00 (840),
# the latest possible start time is 840 - duration = 810.
for t in range(540, 811):
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