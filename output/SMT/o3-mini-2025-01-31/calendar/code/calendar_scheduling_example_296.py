from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes past midnight)

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Ensure that the meeting does not overlap the busy interval.
        s.add(Or(start + duration <= bs, start >= be))

# Albert's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
albert_busy = [(570, 600), (630, 660), (690, 720), (750, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, albert_busy)

# Jessica's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
jessica_busy = [(600, 660), (780, 810), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, jessica_busy)

# Lisa is free the entire day, so no busy intervals.

# Danielle's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:30 to 16:30 -> [810, 990)
danielle_busy = [(570, 630), (660, 720), (810, 990)]
add_busy_constraints(solver, danielle_busy)

# Deborah's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 16:00 -> [900, 960)
deborah_busy = [(540, 630), (660, 690), (780, 840), (900, 960)]
add_busy_constraints(solver, deborah_busy)

# Search for the earliest meeting start time that satisfies the constraints.
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