from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints for a participant.
# For each busy interval [bs, be), the meeting must finish by bs or start after (or at) be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Carolyn's busy intervals:
#   9:30 to 10:30 -> [570, 630)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 17:00 -> [960, 1020)
carolyn_busy = [(570, 630), (810, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, carolyn_busy)

# Jordan's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   10:30 to 11:00 -> [630, 660)
#   13:00 to 14:30 -> [780, 870)
#   16:00 to 16:30 -> [960, 990)
jordan_busy = [(570, 600), (630, 660), (780, 870), (960, 990)]
add_busy_constraints(solver, jordan_busy)

# Wayne's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   12:30 to 13:00 -> [750, 780)
wayne_busy = [(540, 570), (630, 690), (750, 780)]
add_busy_constraints(solver, wayne_busy)

# Megan's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:30 -> [600, 690)
#   12:00 to 13:30 -> [720, 810)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 16:30 -> [960, 990)
megan_busy = [(540, 570), (600, 690), (720, 810), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, megan_busy)

# Billy's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 15:30  -> [690, 930)
#   16:00 to 17:00  -> [960, 1020)
billy_busy = [(540, 660), (690, 930), (960, 1020)]
add_busy_constraints(solver, billy_busy)

# Peter's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:00 to 13:00  -> [660, 780)
#   14:00 to 15:30  -> [840, 930)
#   16:00 to 17:00  -> [960, 1020)
peter_busy = [(540, 630), (660, 780), (840, 930), (960, 1020)]
add_busy_constraints(solver, peter_busy)

# Iterate over all possible start times within work hours to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")