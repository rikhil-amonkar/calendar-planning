from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) should either end before a busy interval
        # starts or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Steven is free the entire day, so no constraints.
# Roy is free the entire day, so no constraints.

# Cynthia's busy intervals:
# 9:30 to 10:30   -> [570, 600)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 13:30  -> [780, 810)
# 15:00 to 16:00  -> [900, 960)
# Note: We use minute counts where 9:30 is 570 etc.
cynthia_busy = [(570, 600), (690, 720), (780, 810), (900, 960)]
add_busy_constraints(solver, cynthia_busy)

# Lauren's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
lauren_busy = [(540, 570), (630, 660), (690, 720), (780, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, lauren_busy)

# Robert's busy intervals:
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 16:00  -> [840, 960)
robert_busy = [(630, 660), (690, 720), (750, 810), (840, 960)]
add_busy_constraints(solver, robert_busy)

# Search for the earliest valid meeting time satisfying all constraints.
solution_found = False
# Latest valid starting time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")