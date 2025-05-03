from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday 9:00 (540 minutes) to 17:00 (1020 minutes)
# Betty prefers the meeting to be before 13:00 (so meeting must end by 13:00, i.e., 780 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes after midnight.

# The meeting must lie within work hours, and because of Betty's preference, finish by 13:00.
solver.add(start >= 540, start + duration <= 1020)
solver.add(start + duration <= 780)  # Betty's preference: meeting must finish by 13:00

# Helper function: Add constraints that ensure the meeting does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must end before a busy interval starts or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Abigail's calendar is wide open, so no busy intervals for her.

# Betty is free the entire day, no busy intervals, but her preference is enforced above.

# Thomas is busy during:
#   9:00 to 9:30  -> from 540 to 570 minutes
#   14:00 to 14:30 -> from 840 to 870 minutes  (though meeting will be before 13:00)
thomas_busy = [(540, 570), (840, 870)]
add_busy_constraints(solver, thomas_busy)

# Albert is busy during:
#   9:30 to 11:00  -> from 570 to 660 minutes
#   12:00 to 13:00 -> from 720 to 780 minutes
#   15:00 to 15:30 -> from 900 to 930 minutes
#   16:00 to 17:00 -> from 960 to 1020 minutes (after Betty's preferred time, but still adding)
albert_busy = [(570, 660), (720, 780), (900, 930), (960, 1020)]
add_busy_constraints(solver, albert_busy)

# Margaret is busy during:
#   9:30 to 10:00   -> from 570 to 600 minutes
#   10:30 to 11:30  -> from 630 to 690 minutes
#   12:30 to 13:00  -> from 750 to 780 minutes
#   13:30 to 15:30  -> from 810 to 930 minutes
#   16:00 to 17:00  -> from 960 to 1020 minutes
margaret_busy = [(570, 600), (630, 690), (750, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, margaret_busy)

# Search for a valid meeting start time.
# Because of Betty's preference, the meeting must end by 780, so valid start times are from 540 to 750.
solution_found = False
for t in range(540, 751):  # meeting start t such that t+30 <= 780
    solver.push()  # Save current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")