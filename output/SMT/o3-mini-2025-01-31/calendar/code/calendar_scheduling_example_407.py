from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must end before the busy interval starts OR start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Alice is free the entire day, so no constraints needed.

# Daniel's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
daniel_busy = [(600, 630), (900, 960), (990, 1020)]
add_busy_constraints(solver, daniel_busy)

# Scott's busy intervals:
# 9:00 to 10:00  -> [540, 600)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
scott_busy = [(540, 600), (720, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, scott_busy)

# Lori's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 16:00 to 16:30 -> [960, 990)
lori_busy = [(750, 780), (960, 990)]
add_busy_constraints(solver, lori_busy)

# Cynthia's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:30 to 16:30 -> [930, 990)
cynthia_busy = [(540, 570), (660, 690), (720, 780), (810, 870), (930, 990)]
add_busy_constraints(solver, cynthia_busy)

# Jeffrey's busy intervals:
# 9:00 to 11:30  -> [540, 690)
# 12:00 to 16:00 -> [720, 960)
# 16:30 to 17:00 -> [990, 1020)
jeffrey_busy = [(540, 690), (720, 960), (990, 1020)]
add_busy_constraints(solver, jeffrey_busy)

# Hannah's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 15:00  -> [780, 900)
# 16:30 to 17:00  -> [990, 1020)
hannah_busy = [(540, 660), (720, 750), (780, 900), (990, 1020)]
add_busy_constraints(solver, hannah_busy)

# We iterate through possible start times (minute by minute) within work hours.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()           # Save the current state of the solver.
    solver.add(start == t)  # Try candidate start time.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")