from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)
# Elijah cannot meet on Monday after 14:30 (870 minutes)
solver.add(start + duration <= 870)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Jason's calendar is free, so no busy constraints for him.

# Elijah's busy intervals (in minutes):
# 12:00 to 14:00 -> [720, 840)
# 14:30 to 15:30 -> [870, 930)  (this interval is not reachable due to the after-14:30 constraint)
# 16:00 to 17:00 -> [960, 1020) (outside the allowed meeting time given Elijah's constraint)
elijah_busy = [
    (720, 840),
    (870, 930),
    (960, 1020)
]
add_busy_constraints(solver, elijah_busy)

# We search for the earliest valid 30-minute meeting time.
found = False
# The meeting must end by 870, so the latest possible start is 870 - 30 = 840.
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