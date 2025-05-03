from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# The meeting must fall within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Add constraints to ensure the meeting does not overlap any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting must either end by the start of a busy interval or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# John's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
john_busy = [(690, 720), (810, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, john_busy)

# Frank's busy intervals:
# 12:00 to 13:30 -> [720, 810)
# 15:00 to 15:30 -> [900, 930)
frank_busy = [(720, 810), (900, 930)]
add_busy_constraints(solver, frank_busy)

# Randy is free, no constraints needed.

# Larry's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
# 16:30 to 17:00  -> [990, 1020)
larry_busy = [(540, 660), (690, 720), (810, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, larry_busy)

# Beverly's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 17:00  -> [810, 1020)
beverly_busy = [(540, 660), (720, 750), (810, 1020)]
add_busy_constraints(solver, beverly_busy)

# Search for a valid meeting start time by iterating through possible start times.
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
        solver.pop()  # Restore the solver state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")