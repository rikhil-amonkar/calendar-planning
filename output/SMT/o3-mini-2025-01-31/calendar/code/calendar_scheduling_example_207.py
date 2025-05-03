from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either finish before busy_start or start after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Walter is free the entire day, so no busy intervals.
# Danielle is free the entire day, so no busy intervals.

# Julia's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 13:30 to 14:00  -> [810, 840)
# 16:00 to 16:30  -> [960, 990)
julia_busy = [(570, 600), (630, 660), (810, 840), (960, 990)]
add_busy_constraints(solver, julia_busy)

# Samuel's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
samuel_busy = [(540, 660), (690, 750), (780, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, samuel_busy)

# Lori's busy intervals:
# 10:00 to 10:30  -> [600, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 17:00  -> [900, 1020)
lori_busy = [(600, 630), (660, 690), (720, 750), (780, 870), (900, 1020)]
add_busy_constraints(solver, lori_busy)

# We want to schedule at the earliest availability.
# Scan through the possible starting times and pick the first candidate that satisfies all constraints.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save current state before trying a candidate.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Format the meeting start and end times as HH:MM.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state before breaking out.
        break
    solver.pop()  # Restore state to try the next candidate.

if not solution_found:
    print("No valid meeting time could be found.")