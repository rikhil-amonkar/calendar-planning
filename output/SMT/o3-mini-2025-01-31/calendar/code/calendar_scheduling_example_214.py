from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either end before a busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Donna is free the entire day, so no busy intervals.
# Susan is also free the entire day.

# Ethan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 16:30 to 17:00 -> [990, 1020)
ethan_busy = [(540, 570), (690, 720), (780, 810), (990, 1020)]
add_busy_constraints(solver, ethan_busy)

# Adam's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:00  -> [780, 840)
# 15:00 to 16:30  -> [900, 990)
adam_busy = [(570, 600), (630, 660), (690, 720), (780, 840), (900, 990)]
add_busy_constraints(solver, adam_busy)

# Jordan's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 16:30  -> [960, 990)
jordan_busy = [(540, 630), (660, 690), (720, 750), (780, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, jordan_busy)

# Search for the earliest valid meeting time satisfying all constraints.
solution_found = False
# The latest valid start is 1020 - duration = 990.
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