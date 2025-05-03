from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function for adding busy time constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting [start, start+duration) does not overlap the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Tyler is free the entire day, so no constraints.
# Kelly is free the entire day, so no constraints.

# Stephanie is busy during:
# 11:00 to 11:30 -> [660, 690)
# 14:30 to 15:00 -> [870, 900)
stephanie_busy = [(660, 690), (870, 900)]
add_busy_constraints(solver, stephanie_busy)

# Joe is busy during:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 17:00 -> [840, 1020)
joe_busy = [(540, 570), (600, 720), (750, 780), (840, 1020)]
add_busy_constraints(solver, joe_busy)

# Diana has meetings during:
# 9:00 to 10:30   -> [540, 630)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 17:00  -> [960, 1020)
diana_busy = [(540, 630), (690, 720), (780, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, diana_busy)

# Deborah is busy during:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 16:30  -> [960, 990)
deborah_busy = [(540, 600), (630, 720), (750, 780), (810, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, deborah_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
for t in range(540, 1020 - duration + 1):
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