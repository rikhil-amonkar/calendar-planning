from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # half an hour meeting
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Deborah's preference: avoid meetings after 14:00.
# We interpret this as the meeting must finish by 14:00 (840 minutes).
solver.add(start + duration <= 840)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # add constraint that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Amber's busy intervals: Amber is free the entire day.
amber_busy = []
add_busy_constraints(solver, amber_busy)

# Deborah's busy intervals (in minutes):
# 9:00 to 11:00  -> [540, 660)
# 11:30 to 15:00 -> [690, 900)
# 15:30 to 17:00 -> [930, 1020)
deborah_busy = [
    (540, 660),
    (690, 900),
    (930, 1020)
]
add_busy_constraints(solver, deborah_busy)

# Search for the earliest valid meeting time.
found = False
latest_start = 1020 - duration  # the latest possible start time

# Since Deborah wants the meeting to finish by 14:00, we can limit our search accordingly.
for t in range(540, 841 - duration):  # up to 840-duration inclusive
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