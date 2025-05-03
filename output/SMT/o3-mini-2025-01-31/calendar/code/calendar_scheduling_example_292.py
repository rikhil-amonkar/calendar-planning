from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap the busy interval if it ends
        # on or before the busy interval starts, or starts on or after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Larry's busy intervals:
#   9:00 to 10:00  -> [540, 600)
#   13:00 to 13:30 -> [780, 810)
#   14:00 to 15:00 -> [840, 900)
#   16:30 to 17:00 -> [990, 1020)
larry_busy = [(540, 600), (780, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, larry_busy)

# Harold's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   15:30 to 16:00 -> [930, 960)
harold_busy = [(690, 720), (930, 960)]
add_busy_constraints(solver, harold_busy)

# Elijah's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:00 -> [690, 720)
elijah_busy = [(600, 630), (690, 720)]
add_busy_constraints(solver, elijah_busy)

# Willie's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:30 to 13:30 -> [690, 810)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 17:00 -> [930, 1020)
willie_busy = [(540, 630), (690, 810), (840, 900), (930, 1020)]
add_busy_constraints(solver, willie_busy)

# Patrick's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 12:30 -> [630, 750)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 17:00 -> [930, 1020)
patrick_busy = [(540, 570), (630, 750), (780, 810), (870, 900), (930, 1020)]
add_busy_constraints(solver, patrick_busy)

# We want the meeting to be scheduled at the earliest availability.
# Iterate over possible start times (in minutes) from 9:00 to the last possible start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to hours and minutes
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")