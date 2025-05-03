from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Janice would rather not meet on Monday after 13:00.
# We'll require that the meeting be finished by 13:00 (780 minutes).
solver.add(start + duration <= 780)

# Helper function to add constraints preventing overlap with busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting does not overlap a busy interval if it ends before the interval starts
        # or starts after (or at) the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Christine's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
christine_busy = [(570, 630), (720, 750), (780, 810), (870, 900), (960, 990)]
add_busy_constraints(solver, christine_busy)

# Janice's calendar is wide open, but she prefers not to meet after 13:00 (already enforced).

# Bobby's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:00 -> [870, 900)
bobby_busy = [(720, 750), (870, 900)]
add_busy_constraints(solver, bobby_busy)

# Elizabeth's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
elizabeth_busy = [(540, 570), (690, 780), (810, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, elizabeth_busy)

# Tyler's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 13:30  -> [780, 810)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
tyler_busy = [(540, 660), (720, 750), (780, 810), (930, 960), (990, 1020)]
add_busy_constraints(solver, tyler_busy)

# Edward's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 14:00 -> [690, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
edward_busy = [(540, 570), (600, 660), (690, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, edward_busy)

# Search for the earliest start time that satisfies all constraints.
found = False
# Given the Janice's constraint, meeting must finish by 13:00, so start is at most 750.
for t in range(540, 751):
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