from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure that the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must either end on or before bs,
        # or start on or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Stephen's busy intervals:
#   11:00 to 12:00 -> [660, 720)
stephen_busy = [(660, 720)]
add_busy_constraints(solver, stephen_busy)

# Diane's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 14:00 -> [780, 840)
#   15:30 to 16:30 -> [930, 990)
diane_busy = [(570, 600), (690, 720), (780, 840), (930, 990)]
add_busy_constraints(solver, diane_busy)

# Joe's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   14:30 to 15:00 -> [870, 900)
joe_busy = [(750, 780), (870, 900)]
add_busy_constraints(solver, joe_busy)

# Diana's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   12:30 to 16:00 -> [750, 960)
diana_busy = [(540, 570), (630, 690), (750, 960)]
add_busy_constraints(solver, diana_busy)

# Julia's busy intervals:
#   9:30 to 12:00  -> [570, 720)
#   12:30 to 17:00 -> [750, 1020)
julia_busy = [(570, 720), (750, 1020)]
add_busy_constraints(solver, julia_busy)

# Stephanie's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 12:00  -> [690, 720)
#   14:30 to 15:00  -> [870, 900)
#   15:30 to 16:00  -> [930, 960)
#   16:30 to 17:00  -> [990, 1020)
stephanie_busy = [(540, 660), (690, 720), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, stephanie_busy)

# Since we're looking for a valid meeting time that works for everyone,
# we iterate over the potential start times (minute by minute) from 9:00 (540) to 16:30 (990).
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