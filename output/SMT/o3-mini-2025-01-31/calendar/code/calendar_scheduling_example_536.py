from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration of 30 minutes
start = Int("start")  # the meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint from Paul:
# Paul cannot meet on Monday before 15:00.
# Therefore, the meeting must start at or after 15:00 (which is 900 minutes).
solver.add(start >= 900)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Logan's busy intervals (in minutes):
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
logan_busy = [
    (630, 660),
    (690, 720),
    (750, 780),
    (810, 840),
    (870, 900),
    (930, 960)
]
add_busy_constraints(solver, logan_busy)

# Paul's busy intervals (in minutes):
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 13:30  -> [720, 810)
# 15:30 to 17:00  -> [930, 1020)
paul_busy = [
    (540, 630),
    (660, 690),
    (720, 810),
    (930, 1020)
]
add_busy_constraints(solver, paul_busy)

# Search for the earliest valid meeting time.
found = False
# The latest possible start time is 1020 - 30 = 990.
for t in range(900, 991):  # start must be >= 900 due to Paul's constraint.
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