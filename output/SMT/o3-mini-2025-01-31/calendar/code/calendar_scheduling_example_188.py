from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')

# Beverly prefers no meetings before 15:00 so we add that constraint.
solver.add(start >= 15 * 60)  # 15:00 is 900 minutes

# Also, the meeting must finish by 17:00.
solver.add(start + duration <= 1020)

# Helper function: for each busy interval [busy_start, busy_end),
# the meeting interval [start, start+duration) must not overlap,
# i.e. either finish by busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Beverly's blocked calendar intervals:
#   10:00 to 11:00  -> [600, 660)
#   13:00 to 13:30  -> [780, 810)
#   15:00 to 15:30  -> [900, 930)
beverly_busy = [(600, 660), (780, 810), (900, 930)]
add_busy_constraints(solver, beverly_busy)

# Brenda's blocked calendar intervals:
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:30  -> [690, 750)
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 15:00  -> [870, 900)
#   16:30 to 17:00  -> [990, 1020)
brenda_busy = [(630, 660), (690, 750), (780, 810), (870, 900), (990, 1020)]
add_busy_constraints(solver, brenda_busy)

# Lori's busy intervals:
#   9:30 to 11:00   -> [570, 660)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 15:30  -> [840, 930)
#   16:00 to 16:30  -> [960, 990)
lori_busy = [(570, 660), (750, 780), (840, 930), (960, 990)]
add_busy_constraints(solver, lori_busy)

# Ronald's blocked calendar intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 15:30  -> [690, 930)
#   16:00 to 17:00  -> [960, 1020)
ronald_busy = [(540, 660), (690, 930), (960, 1020)]
add_busy_constraints(solver, ronald_busy)

# Since Beverly prefers meetings not before 15:00 (900 minutes),
# our search will be from 900 onward.
solution_found = False
# The latest start time is 1020 - duration = 990.
for t in range(900, 991):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")