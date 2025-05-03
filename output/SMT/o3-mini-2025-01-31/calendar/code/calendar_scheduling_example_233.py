from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Mark prefers to avoid meetings after 13:00 (13:00 is 780 minutes),
# so the meeting must finish by 13:00.
solver.add(start + duration <= 780)

# Helper function:
# Given busy intervals (busy_start, busy_end), ensure the meeting [start, start+duration)
# does not overlap any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Samuel's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:00 -> [930, 960)
samuel_busy = [(750, 780), (930, 960)]
add_busy_constraints(solver, samuel_busy)

# Jesse is free the whole day (no busy intervals).

# Willie is free the whole day (no busy intervals).

# Joyce's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 13:00  -> [720, 780)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
joyce_busy = [(570, 600), (660, 690), (720, 780), (840, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, joyce_busy)

# Mark's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 14:00  -> [630, 840)
# 14:30 to 16:00  -> [870, 960)
mark_busy = [(540, 600), (630, 840), (870, 960)]
add_busy_constraints(solver, mark_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Since the meeting must finish by 13:00 (780 minutes), the latest start time is 780 - 30 = 750.
for t in range(540, 751):
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