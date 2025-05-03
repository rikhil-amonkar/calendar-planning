from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either end on/before busy_start or start on/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Michael's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 14:30 to 15:00 -> [870, 900)
michael_busy = [(630, 660), (870, 900)]
add_busy_constraints(solver, michael_busy)

# Samuel's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
samuel_busy = [(630, 660), (750, 780), (810, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, samuel_busy)

# Aaron's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
aaron_busy = [(660, 690), (750, 780), (810, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, aaron_busy)

# Judith's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
judith_busy = [(540, 570), (630, 690), (720, 750), (840, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, judith_busy)

# Kevin's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
kevin_busy = [(540, 660), (690, 780), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, kevin_busy)

# We are looking for the earliest meeting time that works.
solution_found = False
# The latest allowable start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM for display.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")