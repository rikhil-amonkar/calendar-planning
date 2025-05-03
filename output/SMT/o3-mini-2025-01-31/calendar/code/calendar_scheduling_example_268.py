from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end)
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end by the time the busy interval starts, 
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jesse's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 15:30 -> [810, 930)
jesse_busy = [(630, 660), (690, 720), (810, 930)]
add_busy_constraints(solver, jesse_busy)

# Cheryl's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 12:30 to 13:00  -> [750, 780)
# 14:30 to 16:00  -> [870, 960)
# 16:30 to 17:00  -> [990, 1020)
cheryl_busy = [(570, 600), (750, 780), (870, 960), (990, 1020)]
add_busy_constraints(solver, cheryl_busy)

# Elizabeth's calendar is wide open so no busy intervals are added for her.

# Diana's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 17:00  -> [840, 1020)
diana_busy = [(540, 720), (750, 810), (840, 1020)]
add_busy_constraints(solver, diana_busy)

# Barbara's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 16:30  -> [900, 990)
barbara_busy = [(540, 660), (690, 720), (750, 870), (900, 990)]
add_busy_constraints(solver, barbara_busy)

# Attempt to find a valid meeting time by iterating over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore solver state
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")