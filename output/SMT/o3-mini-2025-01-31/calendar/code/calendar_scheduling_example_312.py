from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap a busy interval if it ends before the busy period starts,
        # or starts at or after the busy period ends:
        s.add(Or(start + duration <= bs, start >= be))

# Samantha's busy intervals:
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 12:30 -> [720, 750)
#   15:30 to 16:00 -> [930, 960)
samantha_busy = [(630, 690), (720, 750), (930, 960)]
add_busy_constraints(solver, samantha_busy)

# Jerry's busy intervals:
#   14:00 to 14:30 -> [840, 870)
#   15:30 to 16:00 -> [930, 960)
jerry_busy = [(840, 870), (930, 960)]
add_busy_constraints(solver, jerry_busy)

# Walter is free all day, so no constraints needed.

# Sara's busy intervals:
#   9:30 to 11:30  -> [570, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 15:00 -> [870, 900)
#   16:30 to 17:00 -> [990, 1020)
sara_busy = [(570, 690), (720, 750), (780, 810), (870, 900), (990, 1020)]
add_busy_constraints(solver, sara_busy)

# Kenneth's busy intervals:
#   9:00 to 13:00  -> [540, 780)
#   14:00 to 15:00 -> [840, 900)
#   16:00 to 17:00 -> [960, 1020)
kenneth_busy = [(540, 780), (840, 900), (960, 1020)]
add_busy_constraints(solver, kenneth_busy)

# Danielle's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 13:30 -> [780, 810)
#   14:00 to 16:00 -> [840, 960)
#   16:30 to 17:00 -> [990, 1020)
danielle_busy = [(570, 600), (630, 690), (720, 750), (780, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, danielle_busy)

# Try to find the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # t ranges from 540 to 990 inclusive.
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