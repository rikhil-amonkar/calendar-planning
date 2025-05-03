from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Jacob prefers not to meet before 14:30 (870 minutes).
solver.add(start >= 870)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before the busy interval starts or start on/after its end.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Nathan's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 13:00 to 13:30 -> [780, 810)
nathan_busy = [(630, 660), (780, 810)]
add_busy_constraints(solver, nathan_busy)

# Jacob's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 15:30 to 16:00 -> [930, 960)
jacob_busy = [(780, 810), (930, 960)]
add_busy_constraints(solver, jacob_busy)

# Katherine's busy intervals:
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 15:00 -> [690, 900)
# 15:30 to 16:30 -> [930, 990)
katherine_busy = [(570, 660), (690, 900), (930, 990)]
add_busy_constraints(solver, katherine_busy)

# Samantha's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:30  -> [690, 810)
# 14:00 to 15:30  -> [840, 930)
# 16:00 to 16:30  -> [960, 990)
samantha_busy = [(540, 660), (690, 810), (840, 930), (960, 990)]
add_busy_constraints(solver, samantha_busy)

# Iterate over possible start times (from the Jacob-preferred time onward)
solution_found = False
for t in range(870, 1020 - duration + 1):
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