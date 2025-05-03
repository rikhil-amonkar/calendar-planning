from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration is one hour
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Alexis's busy intervals (in minutes since midnight):
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 14:30  -> [720, 870)
# 15:00 to 16:30  -> [900, 990)
busy_intervals = [
    (540, 660),
    (720, 870),
    (900, 990)
]

# For each busy interval, ensure that the meeting does not overlap.
for b_start, b_end in busy_intervals:
    solver.add(Or(start + duration <= b_start, start >= b_end))

# Search for the earliest valid meeting time.
found = False
# Latest possible start time is 1020 - 60 = 960.
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