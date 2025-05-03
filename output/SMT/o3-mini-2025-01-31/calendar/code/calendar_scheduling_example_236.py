from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours:
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting slot [start, start + duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Gregory: free the entire day so no busy intervals.

# Joyce: free the entire day so no busy intervals.

# Christopher's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 15:00 to 15:30 -> [900, 930)
christopher_busy = [(540, 570), (900, 930)]
add_busy_constraints(solver, christopher_busy)

# Dorothy's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 14:00  -> [660, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:30 to 17:00  -> [990, 1020)
dorothy_busy = [(570, 600), (660, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, dorothy_busy)

# Cynthia's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 13:00 to 15:00  -> [780, 900)
# 15:30 to 16:30  -> [930, 990)
cynthia_busy = [(570, 600), (630, 660), (780, 900), (930, 990)]
add_busy_constraints(solver, cynthia_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The latest start time is 1020 - duration = 990.
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