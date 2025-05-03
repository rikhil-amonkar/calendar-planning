from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# The meeting must be scheduled entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Patrick's preference: he does not want to meet on Monday after 12:00.
# That is, the meeting must finish by 12:00 (i.e. by 720 minutes).
solver.add(start + duration <= 720)

# Helper function to add constraints that ensure a meeting does not overlap a busy interval.
# Each busy interval is given as a tuple (bs, be) where the interval is [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either end on or before bs, or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Marie's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 15:00 -> [750, 900)
marie_busy = [(660, 690), (750, 900)]
add_busy_constraints(solver, marie_busy)

# Mark's busy intervals:
#   11:30 to 12:30 -> [690, 750)
#   15:30 to 16:30 -> [930, 990)
mark_busy = [(690, 750), (930, 990)]
add_busy_constraints(solver, mark_busy)

# Patrick's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   16:00 to 17:00  -> [960, 1020)
patrick_busy = [(570, 600), (630, 660), (690, 720), (750, 780), (960, 1020)]
add_busy_constraints(solver, patrick_busy)

# Julie's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 13:30  -> [720, 810)
#   14:30 to 15:00  -> [870, 900)
#   15:30 to 17:00  -> [930, 1020)
julie_busy = [(540, 600), (660, 690), (720, 810), (870, 900), (930, 1020)]
add_busy_constraints(solver, julie_busy)

# Emma's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 12:30  -> [630, 750)
#   13:30 to 15:00  -> [810, 900)
#   15:30 to 17:00  -> [930, 1020)
emma_busy = [(540, 600), (630, 750), (810, 900), (930, 1020)]
add_busy_constraints(solver, emma_busy)

# Daniel's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 12:00  -> [660, 720)
#   13:30 to 15:00  -> [810, 900)
#   16:30 to 17:00  -> [990, 1020)
daniel_busy = [(540, 600), (660, 720), (810, 900), (990, 1020)]
add_busy_constraints(solver, daniel_busy)

# Now, we iterate over possible meeting start times (minute-by-minute)
# to find a valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")