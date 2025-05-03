from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is one hour, in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Ann's busy intervals (in minutes):
# 9:30 to 10:00 -> [570, 600)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
ann_busy = [(570, 600), (780, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, ann_busy)

# Kathleen's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
kathleen_busy = [(600, 630), (660, 690), (780, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, kathleen_busy)

# Now, search for the earliest valid one-hour meeting time.
found = False
# The meeting must finish by 1020, so the latest start time is 1020 - duration = 1020 - 60 = 960.
for t in range(540, 960 + 1):
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