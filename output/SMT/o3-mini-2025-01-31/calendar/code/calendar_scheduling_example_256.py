from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes since midnight) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval [start, start + duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either end before the busy interval starts, or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Carol is free the whole day, so no busy constraints needed.

# Lori's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 14:00 to 15:00 -> [840, 900)
lori_busy = [(540, 570), (600, 630), (840, 900)]
add_busy_constraints(solver, lori_busy)

# Patricia's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 14:30  -> [840, 870)
patricia_busy = [(570, 600), (750, 810), (840, 870)]
add_busy_constraints(solver, patricia_busy)

# Alexis's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 17:00  -> [900, 1020)
alexis_busy = [(540, 720), (750, 870), (900, 1020)]
add_busy_constraints(solver, alexis_busy)

# Tyler's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:30 to 15:30  -> [750, 930)
# 16:00 to 16:30  -> [960, 990)
tyler_busy = [(540, 690), (750, 930), (960, 990)]
add_busy_constraints(solver, tyler_busy)

# Find the earliest valid meeting start time by iterating over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
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