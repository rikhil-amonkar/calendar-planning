from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Denise does not want to meet before 12:30 (12:30 is 750 minutes).
solver.add(start >= 750)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Jeremy's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
jeremy_busy = [
    (600, 630),
    (660, 720),
    (780, 810),
    (900, 930),
    (990, 1020)
]
add_busy_constraints(solver, jeremy_busy)

# Denise's busy intervals (in minutes):
# 9:00 to 10:00  -> [540, 600)
# 10:30 to 12:00 -> [630, 720)
# 12:30 to 16:00 -> [750, 960)
denise_busy = [
    (540, 600),
    (630, 720),
    (750, 960)
]
add_busy_constraints(solver, denise_busy)

# Search for the earliest valid meeting time.
# Given the constraints, the meeting start must be between max(540,750) = 750 and 1020 - duration = 990.
found = False
for t in range(750, 991):
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