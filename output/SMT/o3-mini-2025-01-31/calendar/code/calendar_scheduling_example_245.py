from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (minutes since midnight)

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting interval [start, start+duration)
# does not overlap with any provided busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before a busy period starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Amanda's busy intervals:
# 14:30 to 15:30 -> [870, 930)
amanda_busy = [(870, 930)]
add_busy_constraints(solver, amanda_busy)

# Margaret's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
margaret_busy = [(660, 690), (840, 870)]
add_busy_constraints(solver, margaret_busy)

# Walter's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 14:30 -> [840, 870)
walter_busy = [(540, 570), (600, 660), (720, 780), (840, 870)]
add_busy_constraints(solver, walter_busy)

# Larry's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:00 -> [690, 780)
# 14:00 to 16:00 -> [840, 960)
# 16:30 to 17:00 -> [990, 1020)
larry_busy = [(540, 660), (690, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, larry_busy)

# John's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
john_busy = [(540, 660), (780, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, john_busy)

# Find the earliest meeting time that fits all constraints.
solution_found = False
for t in range(540, 1020 - duration + 1):
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