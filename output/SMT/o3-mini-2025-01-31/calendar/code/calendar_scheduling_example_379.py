from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish before a busy interval starts, 
        # or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Carolyn's busy intervals:
#   10:30 to 11:30 -> [630, 690)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 15:00 -> [870, 900)
carolyn_busy = [(630, 690), (780, 810), (870, 900)]
add_busy_constraints(solver, carolyn_busy)

# Russell's busy intervals:
#   14:30 to 15:00 -> [870, 900)
#   16:30 to 17:00 -> [990, 1020)
russell_busy = [(870, 900), (990, 1020)]
add_busy_constraints(solver, russell_busy)

# Emma's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   16:30 to 17:00 -> [990, 1020)
emma_busy = [(600, 630), (990, 1020)]
add_busy_constraints(solver, emma_busy)

# Maria's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 11:30  -> [660, 690)
#   12:30 to 14:30  -> [750, 870)
#   15:30 to 17:00  -> [930, 1020)
maria_busy = [(570, 630), (660, 690), (750, 870), (930, 1020)]
add_busy_constraints(solver, maria_busy)

# Mason's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 14:00  -> [720, 840)
#   15:00 to 15:30  -> [900, 930)
mason_busy = [(570, 630), (660, 690), (720, 840), (900, 930)]
add_busy_constraints(solver, mason_busy)

# Hannah's busy intervals:
#   10:00 to 12:30 -> [600, 750)
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 16:00 -> [900, 960)
hannah_busy = [(600, 750), (780, 810), (900, 960)]
add_busy_constraints(solver, hannah_busy)

# Now, iterate over possible meeting start times (minute-by-minute)
# to find a valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")