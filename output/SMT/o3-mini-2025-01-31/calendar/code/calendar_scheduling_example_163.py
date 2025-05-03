from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 to 17:00, which in minutes is from 540 to 1020.
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Define a helper function to add busy intervals.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must either finish before bs or start on/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jason's busy intervals:
# 10:30 to 13:00 -> [630, 780)
# 14:00 to 14:30 -> [840, 870)
jason_busy = [(630, 780), (840, 870)]
add_busy_constraints(solver, jason_busy)

# Hannah has no meetings, so no constraints.

# Gary's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 15:00  -> [630, 900)
# 16:30 to 17:00  -> [990, 1020)
gary_busy = [(540, 600), (630, 900), (990, 1020)]
add_busy_constraints(solver, gary_busy)

# Pamela's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:30  -> [900, 990)
pamela_busy = [(570, 600), (690, 750), (780, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, pamela_busy)

# Now we search for a valid meeting start time that works for everyone.
solution_found = False
for t in range(540, 1020 - duration + 1):
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