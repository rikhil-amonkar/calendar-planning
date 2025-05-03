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
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either end before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Carol's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:30 to 13:30  -> [750, 810)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
carol_busy = [(570, 600), (630, 660), (750, 810), (930, 960), (990, 1020)]
add_busy_constraints(solver, carol_busy)

# Cynthia's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 14:00 to 14:30  -> [840, 870)
# 16:30 to 17:00  -> [990, 1020)
cynthia_busy = [(540, 600), (840, 870), (990, 1020)]
add_busy_constraints(solver, cynthia_busy)

# Judy's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 12:00  -> [660, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 14:30  -> [840, 870)
judy_busy = [(540, 600), (660, 720), (750, 780), (840, 870)]
add_busy_constraints(solver, judy_busy)

# Alan's busy intervals:
# 10:00 to 11:00  -> [600, 660)
# 13:00 to 15:30  -> [780, 930)
# 16:30 to 17:00  -> [990, 1020)
alan_busy = [(600, 660), (780, 930), (990, 1020)]
add_busy_constraints(solver, alan_busy)

# Linda's busy intervals:
# 9:30 to 12:30   -> [570, 750)
# 13:00 to 16:00  -> [780, 960)
linda_busy = [(570, 750), (780, 960)]
add_busy_constraints(solver, linda_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The latest start time is 1020 - 30 = 990.
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