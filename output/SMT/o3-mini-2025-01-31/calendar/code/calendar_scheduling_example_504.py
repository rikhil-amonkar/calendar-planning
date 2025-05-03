from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Alexis prefers to avoid meetings before 11:30 (690 minutes)
solver.add(start >= 690)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start + duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Alexis's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
alexis_busy = [(660, 690), (720, 750), (870, 900), (990, 1020)]
add_busy_constraints(solver, alexis_busy)

# Logan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 17:00 -> [900, 1020)
logan_busy = [(540, 570), (690, 750), (780, 870), (900, 1020)]
add_busy_constraints(solver, logan_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest start time is 1020 - duration.
for t in range(690, 1020 - duration + 1):
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