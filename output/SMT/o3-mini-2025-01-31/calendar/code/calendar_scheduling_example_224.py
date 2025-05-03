from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For a list of busy intervals (each as (busy_start, busy_end)),
# add constraints so that the meeting does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting [start, start+duration) must end before a busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Marilyn's busy intervals:
#   16:00 to 17:00 -> [960, 1020)
marilyn_busy = [(960, 1020)]
add_busy_constraints(solver, marilyn_busy)

# Wayne's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 14:00  -> [780, 840)
wayne_busy = [(570, 600), (630, 690), (720, 750), (780, 840)]
add_busy_constraints(solver, wayne_busy)

# Julia's busy intervals:
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 14:30  -> [840, 870)
julia_busy = [(750, 780), (840, 870)]
add_busy_constraints(solver, julia_busy)

# Deborah's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 14:30  -> [690, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:30 to 17:00  -> [990, 1020)
deborah_busy = [(540, 660), (690, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, deborah_busy)

# Virginia's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 11:30  -> [600, 690)
#   12:30 to 13:30  -> [750, 810)
#   15:00 to 17:00  -> [900, 1020)
virginia_busy = [(540, 570), (600, 690), (750, 810), (900, 1020)]
add_busy_constraints(solver, virginia_busy)

# Search for the earliest valid meeting time satisfying all constraints.
solution_found = False
# The latest valid start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")