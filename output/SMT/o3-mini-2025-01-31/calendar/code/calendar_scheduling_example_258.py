from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Define meeting hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration is 30 minutes.
duration = 30
start = Int("start")  # meeting start time (in minutes since midnight)

# The meeting must be scheduled during work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting interval [start, start+duration)
# does not overlap with a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Either the meeting ends before the busy interval begins, or starts after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Juan's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
juan_busy = [(630, 660), (720, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, juan_busy)

# Marilyn's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 14:00 -> [810, 840)
marilyn_busy = [(660, 690), (810, 840)]
add_busy_constraints(solver, marilyn_busy)

# Brian's busy intervals:
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
brian_busy = [(840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, brian_busy)

# Ruth's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 17:00 -> [780, 1020)
ruth_busy = [(570, 630), (690, 750), (780, 1020)]
add_busy_constraints(solver, ruth_busy)

# Diana's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 12:00 to 16:00 -> [720, 960)
diana_busy = [(570, 690), (720, 960)]
add_busy_constraints(solver, diana_busy)

# Now, try to find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        # Found a meeting time.
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