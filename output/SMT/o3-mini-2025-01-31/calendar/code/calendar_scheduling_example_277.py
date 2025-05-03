from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain meeting to fall within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Adds constraints to ensure the meeting does not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting is valid if it ends before a busy interval starts or starts after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Marilyn is free the entire day, so no constraints for Marilyn.

# Virginia's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 11:30 to 12:00   -> [690, 720)
# 12:30 to 13:00   -> [750, 780)
# 14:30 to 15:00   -> [870, 900)
# 15:30 to 16:00   -> [930, 960)
virginia_busy = [(540, 600), (690, 720), (750, 780), (870, 900), (930, 960)]
add_busy_constraints(solver, virginia_busy)

# Diana has no meetings, so no constraints for Diana.

# Lawrence's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 13:00   -> [630, 780)
# 13:30 to 14:00   -> [810, 840)
# 14:30 to 17:00   -> [870, 1020)
lawrence_busy = [(540, 570), (630, 780), (810, 840), (870, 1020)]
add_busy_constraints(solver, lawrence_busy)

# Angela's busy intervals:
# 9:00 to 10:30    -> [540, 630)
# 11:30 to 13:00   -> [690, 780)
# 13:30 to 16:00   -> [810, 960)
# 16:30 to 17:00   -> [990, 1020)
angela_busy = [(540, 630), (690, 780), (810, 960), (990, 1020)]
add_busy_constraints(solver, angela_busy)

# Search for a valid meeting start time between 9:00 and 17:00.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")