from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constraint: the meeting should be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints ensuring that the meeting time [start, start+duration)
# does not overlap with any busy interval in busy_intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval starts or begin after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jessica: free the whole day. No constraints.

# Joshua's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 16:00 to 16:30 -> [960, 990)
joshua_busy = [(600, 630), (960, 990)]
add_busy_constraints(solver, joshua_busy)

# Robert's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 16:00 to 16:30 -> [960, 990)
robert_busy = [(720, 750), (960, 990)]
add_busy_constraints(solver, robert_busy)

# Samuel's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:30 -> [900, 990)
samuel_busy = [(600, 660), (690, 720), (780, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, samuel_busy)

# Jennifer's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 17:00  -> [900, 1020)
jennifer_busy = [(540, 720), (750, 870), (900, 1020)]
add_busy_constraints(solver, jennifer_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The meeting must finish by 1020, so the latest start time is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")