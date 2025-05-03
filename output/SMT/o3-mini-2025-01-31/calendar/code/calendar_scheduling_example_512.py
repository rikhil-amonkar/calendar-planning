from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Nicholas cannot meet before 15:00.
# That means the meeting must start at or after 15:00 (900 minutes).
solver.add(start >= 900)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration)
        # does not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Paul's busy intervals (in minutes):
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
paul_busy = [(540, 630), (660, 690), (810, 840), (900, 930)]
add_busy_constraints(solver, paul_busy)

# Nicholas' busy intervals (in minutes):
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 14:00 -> [690, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
nicholas_busy = [(570, 660), (690, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, nicholas_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - 30 = 990.
for t in range(900, 991):  # start from 900 due to Nicholas' constraint
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