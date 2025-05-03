from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting slot [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jennifer's calendar is wide open, so no busy intervals.

# Gabriel's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
gabriel_busy = [(780, 810), (840, 870)]
add_busy_constraints(solver, gabriel_busy)

# Andrew's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 16:30 to 17:00 -> [990, 1020)
andrew_busy = [(720, 750), (990, 1020)]
add_busy_constraints(solver, andrew_busy)

# Carolyn's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 17:00  -> [900, 1020)
carolyn_busy = [(540, 660), (720, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, carolyn_busy)

# Alexis's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 17:00  -> [690, 1020)
alexis_busy = [(570, 660), (690, 1020)]
add_busy_constraints(solver, alexis_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Latest possible start time is 1020 - 30 = 990 minutes.
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