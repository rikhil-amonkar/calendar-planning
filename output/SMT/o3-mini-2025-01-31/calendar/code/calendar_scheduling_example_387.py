from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes (9:00 = 540, 17:00 = 1020) and meeting duration (30 minutes).
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Bruce's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 14:30 -> [840, 870)
#   16:00 to 16:30 -> [960, 990)
bruce_busy = [(540, 570), (600, 660), (750, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, bruce_busy)

# Dorothy has no meetings, so no additional constraints.

# Joyce's calendar is wide open, so no constraints.

# Jessica's busy intervals:
#   11:30 to 13:00 -> [690, 780)
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 16:30 -> [870, 990)
jessica_busy = [(690, 780), (810, 840), (870, 990)]
add_busy_constraints(solver, jessica_busy)

# Aaron's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:30 to 12:00  -> [690, 720)
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 15:30  -> [870, 930)
#   16:00 to 16:30  -> [960, 990)
aaron_busy = [(540, 630), (690, 720), (780, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, aaron_busy)

# Kathryn's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 10:30  -> [600, 630)
#   12:30 to 14:00  -> [750, 840)
#   14:30 to 17:00  -> [870, 1020)
kathryn_busy = [(540, 570), (600, 630), (750, 840), (870, 1020)]
add_busy_constraints(solver, kathryn_busy)

# Now, search for the earliest meeting start time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")