from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constraint: the meeting must fall within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish by busy_start or start after busy_end.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jacob is free the entire day, so no constraints needed.

# Virginia's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 16:00 to 17:00 -> [960, 1020)
virginia_busy = [(570, 630), (660, 690), (720, 750), (960, 1020)]
add_busy_constraints(solver, virginia_busy)

# Melissa's busy intervals:
# 11:30 to 12:30 -> [690, 750)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
melissa_busy = [(690, 750), (870, 900), (990, 1020)]
add_busy_constraints(solver, melissa_busy)

# Emma's busy intervals:
# 10:00 to 13:30 -> [600, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 17:00 -> [900, 1020)
emma_busy = [(600, 810), (840, 870), (900, 1020)]
add_busy_constraints(solver, emma_busy)

# Jacqueline's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 14:30 -> [780, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
jacqueline_busy = [(600, 660), (690, 720), (780, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, jacqueline_busy)

# Find a meeting time by iterating through possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state in the solver.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")