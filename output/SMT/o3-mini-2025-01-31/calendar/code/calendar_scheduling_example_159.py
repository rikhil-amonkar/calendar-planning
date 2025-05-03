from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Nathan would like to avoid meetings before 13:00 (780 minutes)
solver.add(start >= 780)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before the busy interval starts or start on/after its end.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Theresa has no meetings - no constraints needed.

# Nathan has no meetings - aside from the preference already added.

# Virginia's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30  -> [690, 750)
# 14:30 to 16:00  -> [870, 960)
# 16:30 to 17:00  -> [990, 1020)
virginia_busy = [(540, 660), (690, 750), (870, 960), (990, 1020)]
add_busy_constraints(solver, virginia_busy)

# Paul's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 14:00  -> [750, 840)
# 15:30 to 16:30  -> [930, 990)
paul_busy = [(540, 570), (630, 660), (690, 720), (750, 840), (930, 990)]
add_busy_constraints(solver, paul_busy)

# Find the earliest valid meeting time from Nathan's preferred start time onward.
solution_found = False
for t in range(780, 1020 - duration + 1):
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