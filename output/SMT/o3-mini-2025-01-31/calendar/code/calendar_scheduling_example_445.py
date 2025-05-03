from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [busy_start, busy_end), the meeting interval
# [start, start+duration) must either finish before busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Sophia's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
sophia_busy = [(660, 690), (720, 750)]
add_busy_constraints(solver, sophia_busy)

# Judith's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 14:30 to 15:00 -> [870, 900)
judith_busy = [(540, 570), (870, 900)]
add_busy_constraints(solver, judith_busy)

# Linda's busy intervals:
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
linda_busy = [(930, 960), (990, 1020)]
add_busy_constraints(solver, linda_busy)

# Ethan is free all day (no busy intervals).

# Anna's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 17:00 -> [810, 1020)
anna_busy = [(540, 570), (600, 660), (690, 750), (810, 1020)]
add_busy_constraints(solver, anna_busy)

# Marie's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
marie_busy = [(570, 600), (630, 690), (720, 750), (780, 810), (840, 870), (900, 960)]
add_busy_constraints(solver, marie_busy)

# Olivia's busy intervals:
# 9:00 to 11:00  -> [540, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 16:00 -> [840, 960)
# 16:30 to 17:00 -> [990, 1020)
olivia_busy = [(540, 660), (690, 750), (780, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, olivia_busy)

# Look for a valid meeting start time by testing each possible minute.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")