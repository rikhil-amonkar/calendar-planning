from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Patricia's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
patricia_busy = [
    (540, 570),
    (600, 630),
    (780, 840),
    (870, 900),
    (930, 960)
]
add_busy_constraints(solver, patricia_busy)

# Austin's busy intervals (in minutes):
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 12:00 -> [630, 720)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
austin_busy = [
    (570, 600),
    (630, 720),
    (780, 840),
    (870, 930),
    (960, 1020)
]
add_busy_constraints(solver, austin_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - duration.
for t in range(540, 1020 - duration + 1):
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