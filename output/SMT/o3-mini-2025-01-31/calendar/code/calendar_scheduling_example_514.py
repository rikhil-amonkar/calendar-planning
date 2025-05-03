from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Nathan would like to avoid more meetings on Monday after 11:00,
# so we add a constraint that the meeting must finish by 11:00, which is 660 minutes.
solver.add(start + duration <= 660)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Martha's busy intervals (in minutes):
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:00 -> [870, 900)
martha_busy = [(720, 750), (870, 900)]
add_busy_constraints(solver, martha_busy)

# Nathan's busy intervals (in minutes):
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:00 -> [930, 960)
nathan_busy = [(540, 630), (660, 690), (720, 780), (810, 840), (930, 960)]
add_busy_constraints(solver, nathan_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# Due to the constraint that the meeting must finish by 660, the latest possible start is 630.
for t in range(540, 631):
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