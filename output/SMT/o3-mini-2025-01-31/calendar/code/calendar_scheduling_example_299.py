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

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap with any busy interval if it ends before
        # the interval starts OR starts after or at the interval end.
        s.add(Or(start + duration <= bs, start >= be))

# Jacqueline's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 16:30 to 17:00 -> [990, 1020)
jacqueline_busy = [(540, 570), (630, 690), (720, 750), (780, 810), (990, 1020)]
add_busy_constraints(solver, jacqueline_busy)

# Lauren's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:00 -> [930, 960)
lauren_busy = [(600, 660), (690, 750), (810, 840), (930, 960)]
add_busy_constraints(solver, lauren_busy)

# Billy is free the entire day, so no busy intervals.

# Mark's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 14:30 -> [690, 870)
# 15:00 to 16:00 -> [900, 960)
mark_busy = [(570, 630), (690, 870), (900, 960)]
add_busy_constraints(solver, mark_busy)

# Teresa's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 14:00 -> [720, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
teresa_busy = [(540, 570), (630, 690), (720, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, teresa_busy)

# Find the earliest valid meeting start time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert the meeting start/end from minutes to HH:MM.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")