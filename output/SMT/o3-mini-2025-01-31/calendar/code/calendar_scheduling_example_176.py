from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Ensure meeting [start, start+duration) does not overlap with busy interval [bs, be)
        solver.add(Or(start + duration <= bs, start >= be))

# Gary's busy intervals.
# 9:00 to 9:30 -> [540, 570)
# 14:00 to 14:30 -> [840, 870)
gary_busy = [(540, 570), (840, 870)]
add_busy_constraints(solver, gary_busy)

# Melissa's busy intervals.
# 12:00 to 13:00 -> [720, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
melissa_busy = [(720, 780), (870, 900), (960, 990)]
add_busy_constraints(solver, melissa_busy)

# Alan's busy intervals.
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 17:00  -> [720, 1020)
alan_busy = [(540, 600), (630, 690), (720, 1020)]
add_busy_constraints(solver, alan_busy)

# Kevin's busy intervals.
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 16:00 -> [720, 960)
kevin_busy = [(540, 570), (600, 630), (720, 960)]
add_busy_constraints(solver, kevin_busy)

# Try to find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # save current solver state
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # restore state
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")