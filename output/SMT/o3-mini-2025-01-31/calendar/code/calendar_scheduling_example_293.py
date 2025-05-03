from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Vincent's additional constraint: do not want to meet on Monday after 14:30.
# We enforce that the meeting must finish by 14:30 (i.e., 870 minutes).
solver.add(start + duration <= 870)

# Helper function to add constraints ensuring the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting and a busy interval do not overlap if
        # the meeting ends on or before the busy interval starts,
        # or the meeting starts on or after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Scott is free the entire day: no busy intervals.

# Nicholas's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   15:30 to 16:00 -> [930, 960)
nicholas_busy = [(660, 690), (930, 960)]
add_busy_constraints(solver, nicholas_busy)

# Donna's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   12:00 to 12:30 -> [720, 750)
#   14:00 to 14:30 -> [840, 870)
#   16:00 to 16:30 -> [960, 990)
donna_busy = [(570, 600), (720, 750), (840, 870), (960, 990)]
add_busy_constraints(solver, donna_busy)

# Vincent's busy intervals:
#   9:30 to 11:00  -> [570, 660)
#   11:30 to 12:00 -> [690, 720)
#   13:30 to 14:30 -> [810, 870)
#   15:30 to 16:30 -> [930, 990)
vincent_busy = [(570, 660), (690, 720), (810, 870), (930, 990)]
add_busy_constraints(solver, vincent_busy)

# Ann's busy intervals:
#   9:30 to 11:00  -> [570, 660)
#   12:00 to 13:00 -> [720, 780)
#   14:00 to 15:00 -> [840, 900)
#   16:30 to 17:00 -> [990, 1020)
ann_busy = [(570, 660), (720, 780), (840, 900), (990, 1020)]
add_busy_constraints(solver, ann_busy)

# We want to schedule the meeting at the earliest availability.
# Because of Vincent's constraint, meeting must finish by 14:30.
# So the meeting start must be between 9:00 (540) and 14:00 (840).
found = False
for t in range(540, 841):  # 841 because start + 30 must be <= 870
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