from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration of 1 hour
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to fall within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Ann's calendar is free the entire day, so no busy constraints.
# Christopher's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
christopher_busy = [
    (540, 600),
    (660, 690),
    (720, 750),
    (780, 810),
    (840, 870),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, christopher_busy)

# The group wants the meeting at the earliest availability.
# We'll search for the earliest start time that satisfies all constraints.
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