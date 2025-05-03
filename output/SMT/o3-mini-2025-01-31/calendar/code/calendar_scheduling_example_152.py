from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Sarah prefers not to meet before 13:30 (810 minutes)
solver.add(start >= 810)

# Helper function: for each busy interval [bs, be),
# add a constraint so that the meeting [start, start+duration)
# does not overlap with that busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Aaron's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 14:00 -> [750, 840)
# 15:30 to 16:00 -> [930, 960)
aaron_busy = [(540, 570), (690, 720), (750, 840), (930, 960)]
add_busy_constraints(solver, aaron_busy)

# Sarah's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:30 -> [810, 870)
# 16:00 to 16:30 -> [960, 990)
sarah_busy = [(630, 690), (750, 780), (810, 870), (960, 990)]
add_busy_constraints(solver, sarah_busy)

# Martha's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 17:00  -> [930, 1020)
martha_busy = [(540, 570), (630, 720), (750, 810), (840, 870), (930, 1020)]
add_busy_constraints(solver, martha_busy)

# Heather's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 16:30  -> [960, 990)
heather_busy = [(540, 600), (690, 720), (780, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, heather_busy)

# Iterate over possible start times (in minutes) from max constraint (810) to the latest valid start time.
solution_found = False
for t in range(810, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")