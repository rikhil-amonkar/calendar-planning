from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes (9:00 = 540, 17:00 = 1020) and the meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Ensure the meeting is entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must either end on or before bs
        # or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Amy has no meetings, so no busy intervals.
# Karen's busy intervals:
#   9:30 to 10:00  -> from 570 to 600 minutes,
#   12:30 to 13:00 -> from 750 to 780 minutes.
karen_busy = [(570, 600), (750, 780)]
add_busy_constraints(solver, karen_busy)

# Mark's busy intervals:
#   10:30 to 11:30 -> from 630 to 690 minutes,
#   13:00 to 13:30 -> from 780 to 810 minutes,
#   15:30 to 16:00 -> from 930 to 960 minutes.
mark_busy = [(630, 690), (780, 810), (930, 960)]
add_busy_constraints(solver, mark_busy)

# Madison's busy intervals:
#   9:00 to 12:00   -> from 540 to 720 minutes,
#   12:30 to 13:30  -> from 750 to 810 minutes,
#   15:30 to 16:00  -> from 930 to 960 minutes,
#   16:30 to 17:00  -> from 990 to 1020 minutes.
madison_busy = [(540, 720), (750, 810), (930, 960), (990, 1020)]
add_busy_constraints(solver, madison_busy)

# Michelle's busy intervals:
#   9:00 to 9:30    -> from 540 to 570 minutes,
#   10:00 to 10:30  -> from 600 to 630 minutes,
#   11:00 to 11:30  -> from 660 to 690 minutes,
#   12:00 to 14:00  -> from 720 to 840 minutes,
#   14:30 to 15:00  -> from 870 to 900 minutes,
#   15:30 to 16:30  -> from 930 to 990 minutes.
michelle_busy = [(540, 570), (600, 630), (660, 690), (720, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, michelle_busy)

# Brandon's busy intervals:
#   9:30 to 15:00   -> from 570 to 900 minutes,
#   15:30 to 17:00  -> from 930 to 1020 minutes.
brandon_busy = [(570, 900), (930, 1020)]
add_busy_constraints(solver, brandon_busy)

# Find the earliest valid meeting time by iterating over possible start times (minute-by-minute).
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