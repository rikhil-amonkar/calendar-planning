from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for each busy interval.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must either end before busy_start or start after or at busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Lisa's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:30 to 14:00  -> [810, 840)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 16:30  -> [960, 990)
lisa_busy = [(570, 600), (630, 660), (690, 720), (810, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, lisa_busy)

# Joshua's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 15:00 -> [840, 900)
joshua_busy = [(540, 570), (690, 720), (840, 900)]
add_busy_constraints(solver, joshua_busy)

# James's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 12:00  -> [660, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 15:00  -> [840, 900)
# 16:30 to 17:00  -> [990, 1020)
james_busy = [(540, 630), (660, 720), (750, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, james_busy)

# Steven's busy intervals:
# 9:00 to 14:00   -> [540, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 17:00  -> [960, 1020)
steven_busy = [(540, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, steven_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")