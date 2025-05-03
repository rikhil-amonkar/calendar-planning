from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Nicole prefers not to meet before 16:00.
# Therefore, the meeting must start at or after 16:00 (960 minutes).
solver.add(start >= 960)

# Helper function to add busy interval constraints.
# The meeting interval [start, start + duration) must not overlap with [b_start, b_end)
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Nicole's busy intervals (in minutes):
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 15:30 to 16:00 -> [930, 960)
nicole_busy = [(660, 690), (720, 780), (930, 960)]
add_busy_constraints(solver, nicole_busy)

# Arthur's busy intervals (in minutes):
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:30 to 15:00 -> [810, 900)
# 16:30 to 17:00 -> [990, 1020)
arthur_busy = [(570, 630), (660, 720), (810, 900), (990, 1020)]
add_busy_constraints(solver, arthur_busy)

# Now, search for the earliest valid 30-minute meeting time.
found = False
# Because the meeting must finish by 1020, the latest possible start time is 1020 - 30 = 990.
# And considering Nicole's preference, we begin at 960.
for t in range(960, 990 + 1):
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