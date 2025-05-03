from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either end on or before bs, or start on or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Larry's busy intervals:
#   9:30 to 10:30 -> [570, 630)
#   12:30 to 13:00 -> [750, 780)
#   15:30 to 16:00 -> [930, 960)
larry_busy = [(570, 630), (750, 780), (930, 960)]
add_busy_constraints(solver, larry_busy)

# Julie's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   16:00 to 16:30 -> [960, 990)
julie_busy = [(660, 690), (960, 990)]
add_busy_constraints(solver, julie_busy)

# Jason's busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   16:00 to 16:30 -> [960, 990)
jason_busy = [(540, 570), (960, 990)]
add_busy_constraints(solver, jason_busy)

# Mason's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 13:30 -> [720, 810)
#   15:00 to 16:30 -> [900, 990)
mason_busy = [(600, 630), (660, 690), (720, 810), (900, 990)]
add_busy_constraints(solver, mason_busy)

# Alan's busy intervals:
#   9:00 to 11:30  -> [540, 690)
#   12:00 to 14:00 -> [720, 840)
#   14:30 to 17:00 -> [870, 1020)
alan_busy = [(540, 690), (720, 840), (870, 1020)]
add_busy_constraints(solver, alan_busy)

# Bruce's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   11:30 to 13:00 -> [690, 780)
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 16:30 -> [960, 990)
bruce_busy = [(570, 600), (690, 780), (810, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, bruce_busy)

# Iterate over possible meeting start times (minute-by-minute) to find a valid time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}" \
              .format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")