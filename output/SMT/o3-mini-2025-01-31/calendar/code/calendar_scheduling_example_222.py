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

# Helper function to add non-overlap constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Betty's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
betty_busy = [(570, 600), (630, 660), (870, 900), (930, 960)]
add_busy_constraints(solver, betty_busy)

# Evelyn's busy intervals:
# 11:30 to 12:30  -> [690, 750)
# 14:00 to 15:00  -> [840, 900)
evelyn_busy = [(690, 750), (840, 900)]
add_busy_constraints(solver, evelyn_busy)

# John's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 13:30  -> [780, 810)
# 15:00 to 16:00  -> [900, 960)
john_busy = [(570, 600), (630, 660), (690, 720), (780, 810), (900, 960)]
add_busy_constraints(solver, john_busy)

# Andrea's busy intervals:
# 10:30 to 13:00 -> [630, 780)
# 13:30 to 17:00 -> [810, 1020)
andrea_busy = [(630, 780), (810, 1020)]
add_busy_constraints(solver, andrea_busy)

# Eric's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:30 -> [930, 990)
eric_busy = [(600, 630), (660, 720), (780, 810), (840, 900), (930, 990)]
add_busy_constraints(solver, eric_busy)

# Search for the earliest valid meeting time satisfying all constraints.
solution_found = False
# Latest valid start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current state.
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