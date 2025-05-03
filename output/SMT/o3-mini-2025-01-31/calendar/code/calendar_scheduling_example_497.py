from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Robert is free the whole day, so no constraints.

# Kyle's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:00  -> [690, 720)
# 14:00 to 15:00  -> [840, 900)
kyle_busy = [(570, 600), (690, 720), (840, 900)]
add_busy_constraints(solver, kyle_busy)

# Russell's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:00  -> [630, 660)
# 12:00 to 12:30  -> [720, 750)
# 16:00 to 16:30  -> [960, 990)
russell_busy = [(540, 570), (630, 660), (720, 750), (960, 990)]
add_busy_constraints(solver, russell_busy)

# Juan's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 15:00  -> [870, 900)
juan_busy = [(690, 720), (780, 840), (870, 900)]
add_busy_constraints(solver, juan_busy)

# Beverly's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 15:30  -> [900, 930)
beverly_busy = [(540, 600), (630, 690), (780, 870), (900, 930)]
add_busy_constraints(solver, beverly_busy)

# Bryan's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 17:00  -> [780, 1020)
bryan_busy = [(540, 570), (630, 690), (720, 750), (780, 1020)]
add_busy_constraints(solver, bryan_busy)

# Margaret's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 17:00  -> [750, 1020)
margaret_busy = [(540, 600), (630, 720), (750, 1020)]
add_busy_constraints(solver, margaret_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")