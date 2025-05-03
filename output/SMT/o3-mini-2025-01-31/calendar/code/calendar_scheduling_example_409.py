from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Mason's preference: does not want to meet after 14:00;
# so the meeting must end by 14:00 (840 minutes).
solver.add(start + duration <= 840)

# Helper function: add constraints such that the meeting does not overlap any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting [start, start+duration) must either end before the busy interval begins
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Alan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
alan_busy = [(540, 570), (600, 660), (690, 720)]
add_busy_constraints(solver, alan_busy)

# Mason's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 16:30 to 17:00 -> [990, 1020)
mason_busy = [(810, 840), (990, 1020)]
add_busy_constraints(solver, mason_busy)

# Dennis's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 14:30 to 15:00 -> [870, 900)
dennis_busy = [(540, 570), (870, 900)]
add_busy_constraints(solver, dennis_busy)

# Theresa is free the entire day, so no constraints.

# Brenda's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 13:30 -> [720, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
brenda_busy = [(630, 660), (720, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, brenda_busy)

# Juan's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 13:00  -> [690, 780)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 17:00  -> [960, 1020)
juan_busy = [(570, 600), (630, 660), (690, 780), (870, 900), (960, 1020)]
add_busy_constraints(solver, juan_busy)

# Angela's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:00  -> [780, 840)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
angela_busy = [(540, 600), (630, 660), (690, 720), (780, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, angela_busy)

# Since Mason's preference forces meeting to finish by 14:00 (840 minutes),
# the candidate start times range from 540 to 810 (inclusive).
found = False
for t in range(540, 810 + 1):
    solver.push()           # Save current solver state.
    solver.add(start == t)  # Try candidate starting time.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state.
        break
    solver.pop()      # Restore state if candidate fails.

if not found:
    print("No valid meeting time could be found.")