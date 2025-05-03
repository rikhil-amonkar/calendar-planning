from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting slot [start, start+duration)
# does not overlap with any busy interval (busy_start, busy_end).
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Joyce: free the entire day, so no busy intervals.

# Judith's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 14:30 to 15:00 -> [870, 900)
judith_busy = [(540, 570), (870, 900)]
add_busy_constraints(solver, judith_busy)

# Bradley's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
bradley_busy = [(600, 630), (840, 870), (900, 960)]
add_busy_constraints(solver, bradley_busy)

# Terry's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 17:00  -> [900, 1020)
terry_busy = [(540, 720), (750, 870), (900, 1020)]
add_busy_constraints(solver, terry_busy)

# Hannah's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 15:00 -> [840, 900)
# 16:00 to 16:30 -> [960, 990)
hannah_busy = [(540, 570), (600, 630), (660, 720), (750, 780), (840, 900), (960, 990)]
add_busy_constraints(solver, hannah_busy)

# Search for the earliest valid meeting time (in minutes).
solution_found = False
# Latest possible start time is 1020 - 30 = 990.
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