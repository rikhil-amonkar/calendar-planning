from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Jean prefers to avoid meetings after 15:30, so the meeting must finish by 15:30 (930 minutes).
# Meeting duration is 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Jean's preference: meeting should finish by 15:30.
solver.add(start + duration <= 930)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before the busy interval starts or start after it ends.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jennifer's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:00 -> [930, 960)
jennifer_busy = [(750, 780), (930, 960)]
add_busy_constraints(solver, jennifer_busy)

# Jean's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
jean_busy = [(720, 750), (780, 810), (840, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, jean_busy)

# Jerry's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
jerry_busy = [(540, 570), (600, 660), (690, 720), (780, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, jerry_busy)

# Carl's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:30 to 16:00  -> [930, 960)
carl_busy = [(540, 660), (720, 780), (810, 840), (930, 960)]
add_busy_constraints(solver, carl_busy)

# Now, search for the earliest valid meeting start time (in minutes from midnight) that satisfies all constraints.
solution_found = False
# Given Jean's constraint (meeting finishes by 15:30), the latest valid start is 900.
for t in range(540, 901):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")