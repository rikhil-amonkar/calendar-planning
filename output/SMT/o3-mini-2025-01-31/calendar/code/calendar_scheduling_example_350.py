from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must start and end within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For any busy interval [bs, be), the meeting must either end at or before bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Madison's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 16:00 -> [930, 960)
madison_busy = [(540, 570), (840, 900), (930, 960)]
add_busy_constraints(solver, madison_busy)

# Cheryl is free the whole day (no busy intervals).

# Walter is free the whole day (no busy intervals).

# Donna's busy intervals:
#   9:30 to 11:00  -> [570, 660)
#   11:30 to 15:00 -> [690, 900)
#   16:00 to 17:00 -> [960, 1020)
donna_busy = [(570, 660), (690, 900), (960, 1020)]
add_busy_constraints(solver, donna_busy)

# Kathleen's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 15:00 -> [660, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
kathleen_busy = [(540, 570), (600, 630), (660, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, kathleen_busy)

# Samuel's busy intervals:
#   9:30 to 12:30  -> [570, 750)
#   13:00 to 13:30 -> [780, 810)
#   15:30 to 17:00 -> [930, 1020)
samuel_busy = [(570, 750), (780, 810), (930, 1020)]
add_busy_constraints(solver, samuel_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Format meeting time in HH:MM.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")