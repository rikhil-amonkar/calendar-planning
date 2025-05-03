from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure meeting is within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish on or before the busy interval starts
        # or start on or after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Debra's busy intervals:
#   13:00 to 14:30 -> [780, 870)
#   16:30 to 17:00 -> [990, 1020)
debra_busy = [(780, 870), (990, 1020)]
add_busy_constraints(solver, debra_busy)

# Ryan has no meetings, so no busy intervals.

# Maria's busy intervals:
#   12:00 to 12:30 -> [720, 750)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 16:00 -> [930, 960)
maria_busy = [(720, 750), (840, 900), (930, 960)]
add_busy_constraints(solver, maria_busy)

# Timothy's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   11:00 to 13:00  -> [660, 780)
#   13:30 to 15:00  -> [810, 900)
#   15:30 to 16:30  -> [930, 990)
timothy_busy = [(570, 600), (660, 780), (810, 900), (930, 990)]
add_busy_constraints(solver, timothy_busy)

# Pamela's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 15:00  -> [840, 900)
#   15:30 to 17:00  -> [930, 1020)
pamela_busy = [(600, 660), (750, 780), (840, 900), (930, 1020)]
add_busy_constraints(solver, pamela_busy)

# Ethan's busy intervals:
#   9:30 to 11:00   -> [570, 660)
#   11:30 to 14:00  -> [690, 840)
#   14:30 to 15:30  -> [870, 930)
#   16:00 to 17:00  -> [960, 1020)
ethan_busy = [(570, 660), (690, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, ethan_busy)

# Iterate over possible meeting start times minute-by-minute.
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