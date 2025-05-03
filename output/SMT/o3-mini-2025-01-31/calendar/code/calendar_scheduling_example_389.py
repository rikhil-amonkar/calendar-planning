from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define meeting parameters: working hours 9:00 (540) to 17:00 (1020) and duration 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure meeting is fully within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval [bs, be),
# enforce that the meeting either ends before bs or starts after the busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Debra's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   13:30 to 14:00 -> [810, 840)
debra_busy = [(660, 690), (810, 840)]
add_busy_constraints(solver, debra_busy)

# Sara's calendar is wide open, so no constraints.

# Theresa's busy intervals:
#   13:30 to 14:00 -> [810, 840)
#   15:30 to 16:00 -> [930, 960)
theresa_busy = [(810, 840), (930, 960)]
add_busy_constraints(solver, theresa_busy)

# Carol's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 13:30  -> [720, 810)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 16:30  -> [960, 990)
carol_busy = [(540, 600), (660, 690), (720, 810), (900, 930), (960, 990)]
add_busy_constraints(solver, carol_busy)

# Justin's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 14:00 -> [600, 840)
#   14:30 to 15:30 -> [870, 930)
#   16:30 to 17:00 -> [990, 1020)
justin_busy = [(540, 570), (600, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, justin_busy)

# Edward's busy intervals:
#   9:30 to 10:30 -> [570, 630)
#   11:30 to 13:00 -> [690, 780)
#   13:30 to 14:00 -> [810, 840)
#   16:00 to 17:00 -> [960, 1020)
edward_busy = [(570, 630), (690, 780), (810, 840), (960, 1020)]
add_busy_constraints(solver, edward_busy)

# Search for an earliest possible meeting time by iterating minute-by-minute.
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