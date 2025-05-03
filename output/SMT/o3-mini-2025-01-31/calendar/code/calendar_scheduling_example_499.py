from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within work hours.
# Also, Samuel prefers not to have meetings after 15:00, so the meeting must end by 15:00 (900 minutes).
solver.add(start >= 540, start + duration <= 1020, start + duration <= 900)

# Helper function to add constraints that the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Patrick's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
patrick_busy = [(750, 780), (870, 900)]
add_busy_constraints(solver, patrick_busy)

# Alice's calendar is wide open (no constraints).

# Samuel's calendar is wide open.
# However, Samuel prefers to avoid meetings after 15:00. (Constraint added above.)

# Joyce's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 15:00 to 15:30 -> [900, 930)  (This one is not relevant if meeting ends by 15:00)
joyce_busy = [(540, 570), (600, 630), (690, 720), (900, 930)]
add_busy_constraints(solver, joyce_busy)

# Peter's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 13:30 -> [720, 810)
# 16:00 to 17:00 -> [960, 1020)
peter_busy = [(570, 600), (630, 690), (720, 810), (960, 1020)]
add_busy_constraints(solver, peter_busy)

# Hannah's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:30 to 12:30 -> [690, 750)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
hannah_busy = [(540, 630), (690, 750), (900, 930), (960, 1020)]
add_busy_constraints(solver, hannah_busy)

# Joseph's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
joseph_busy = [(570, 600), (720, 780), (810, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, joseph_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# The meeting must finish by 900, so the latest start time is 900 - duration = 870.
for t in range(540, 870 + 1):
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