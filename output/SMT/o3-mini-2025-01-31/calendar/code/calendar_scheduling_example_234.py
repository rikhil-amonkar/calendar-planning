from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function:
# Given a list of busy intervals (each as (busy_start, busy_end)), ensures that
# the meeting slot [start, start+duration) does NOT overlap the busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Catherine is free all day - no busy constraints.

# Barbara's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 11:30  -> [660, 690)
# 14:00 to 14:30  -> [840, 870)
# 16:30 to 17:00  -> [990, 1020)
barbara_busy = [(570, 600), (660, 690), (840, 870), (990, 1020)]
add_busy_constraints(solver, barbara_busy)

# Bruce's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 16:30  -> [960, 990)
bruce_busy = [(690, 720), (750, 780), (870, 900), (960, 990)]
add_busy_constraints(solver, bruce_busy)

# Robert's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 13:30  -> [660, 810)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:30  -> [930, 990)
robert_busy = [(570, 630), (660, 810), (870, 900), (930, 990)]
add_busy_constraints(solver, robert_busy)

# Michelle's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 14:30  -> [660, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
michelle_busy = [(540, 600), (660, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, michelle_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The latest start time is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")