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

# Helper function to ensure the meeting does not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish before a busy interval begins,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jennifer's busy intervals:
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:30 to 17:00  -> [990, 1020)
jennifer_busy = [(720, 780), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, jennifer_busy)

# Gregory's calendar is wide open (no busy intervals).

# Stephanie is free the whole day, no busy intervals.

# Lori's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:30 -> [840, 930)
# 16:30 to 17:00 -> [990, 1020)
lori_busy = [(540, 570), (660, 690), (720, 750), (780, 810), (840, 930), (990, 1020)]
add_busy_constraints(solver, lori_busy)

# Jessica's busy intervals:
# 9:00 to 11:30  -> [540, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 16:30 -> [900, 990)
jessica_busy = [(540, 690), (720, 780), (810, 870), (900, 990)]
add_busy_constraints(solver, jessica_busy)

# Find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")