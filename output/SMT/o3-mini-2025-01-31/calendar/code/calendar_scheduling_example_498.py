from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Diana is free the entire day, so no constraints.

# Richard's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:30 to 15:00 -> [870, 900)
richard_busy = [(660, 690), (870, 900)]
add_busy_constraints(solver, richard_busy)

# Judith's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 15:00 to 15:30 -> [900, 930)
judith_busy = [(540, 570), (900, 930)]
add_busy_constraints(solver, judith_busy)

# Ryan's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 16:30 to 17:00 -> [990, 1020)
ryan_busy = [(780, 810), (990, 1020)]
add_busy_constraints(solver, ryan_busy)

# Alexis's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 15:00  -> [810, 900)
# 16:00 to 17:00  -> [960, 1020)
alexis_busy = [(540, 600), (630, 660), (720, 780), (810, 900), (960, 1020)]
add_busy_constraints(solver, alexis_busy)

# Donna's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 11:30 to 13:30  -> [690, 810)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 17:00  -> [960, 1020)
donna_busy = [(540, 570), (690, 810), (870, 900), (960, 1020)]
add_busy_constraints(solver, donna_busy)

# Jason's busy intervals:
# 9:00 to 12:30   -> [540, 750)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 15:00  -> [870, 900)
jason_busy = [(540, 750), (780, 840), (870, 900)]
add_busy_constraints(solver, jason_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
# Iterate over possible meeting start times from 9:00 (540) to the latest start time (1020-duration)
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