from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval [bs, be), enforce that the meeting does not overlap
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Lori's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 12:30  -> [720, 750)
#   13:30 to 14:30  -> [810, 870)
#   16:30 to 17:00  -> [990, 1020)
lori_busy = [(570, 600), (660, 690), (720, 750), (810, 870), (990, 1020)]
add_busy_constraints(solver, lori_busy)

# Victoria is free all day, so no busy intervals.

# Natalie is wide open all day, so no busy intervals.

# Pamela's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 12:00  -> [660, 720)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 15:00  -> [840, 900)
#   16:30 to 17:00  -> [990, 1020)
pamela_busy = [(570, 630), (660, 720), (780, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, pamela_busy)

# Justin's busy intervals:
#   9:00 to 10:00    -> [540, 600)
#   10:30 to 11:30   -> [630, 690)
#   12:00 to 13:00   -> [720, 780)
#   13:30 to 15:00   -> [810, 900)
#   15:30 to 17:00   -> [930, 1020)
justin_busy = [(540, 600), (630, 690), (720, 780), (810, 900), (930, 1020)]
add_busy_constraints(solver, justin_busy)

# Martha's busy intervals:
#   9:00 to 11:30    -> [540, 690)
#   12:30 to 13:00   -> [750, 780)
#   13:30 to 15:00   -> [810, 900)
#   15:30 to 16:00   -> [930, 960)
martha_busy = [(540, 690), (750, 780), (810, 900), (930, 960)]
add_busy_constraints(solver, martha_busy)

# Now, iterate over possible start times (minute by minute) to find a valid meeting time.
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