from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint from Edward:
# Edward would like to avoid more meetings on Monday after 14:30.
# Thus, the meeting must finish by 14:30 (870 minutes).
solver.add(start + duration <= 870)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end),
    # ensure that the meeting interval [start, start+duration) does not overlap with it.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Harold's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:00 -> [930, 960)
harold_busy = [
    (600, 630),
    (660, 690),
    (810, 840),
    (930, 960)
]
add_busy_constraints(solver, harold_busy)

# Edward's busy intervals (in minutes):
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
edward_busy = [
    (540, 690),
    (720, 750),
    (780, 870),
    (900, 930),
    (960, 1020)
]
add_busy_constraints(solver, edward_busy)

# Search for the earliest valid meeting time.
found = False
# With the constraint that meeting must finish by 870 (14:30),
# the latest possible start is 870 - duration = 840.
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