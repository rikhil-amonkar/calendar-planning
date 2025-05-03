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

# Thomas's preference: avoid meetings before 10:30 (i.e. 630 minutes).
solver.add(start >= 630)

# Helper function to add constraints ensuring the meeting does not overlap a given busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap a busy interval if it ends before bs or starts after or at be.
        s.add(Or(start + duration <= bs, start >= be))

# Carolyn's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 16:00 -> [900, 960)
carolyn_busy = [(600, 630), (720, 780), (810, 840), (900, 960)]
add_busy_constraints(solver, carolyn_busy)

# Mark's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:00 to 15:30 -> [900, 930)
mark_busy = [(750, 780), (900, 930)]
add_busy_constraints(solver, mark_busy)

# Thomas is free the entire day, so no busy intervals for him.

# Hannah's busy intervals:
# 9:30 to 11:00  -> [570, 660)
# 12:00 to 15:30 -> [720, 930)
# 16:00 to 17:00 -> [960, 1020)
hannah_busy = [(570, 660), (720, 930), (960, 1020)]
add_busy_constraints(solver, hannah_busy)

# Abigail's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 15:00 -> [780, 900)
# 16:00 to 16:30 -> [960, 990)
abigail_busy = [(570, 630), (720, 750), (780, 900), (960, 990)]
add_busy_constraints(solver, abigail_busy)

# Try to find the earliest meeting start time that satisfies all constraints.
found = False
# We know from Thomas's constraint that meeting start gte 630, so iterate from 630 to last possible start.
for t in range(630, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes back to hours and minutes for output.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")