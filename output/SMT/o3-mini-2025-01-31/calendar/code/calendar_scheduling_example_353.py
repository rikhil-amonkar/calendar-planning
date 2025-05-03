from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to start and finish within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting must either finish at or before bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Andrea's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:30 -> [690, 750)
#   14:30 to 15:00 -> [870, 900)
andrea_busy = [(600, 630), (690, 750), (870, 900)]
add_busy_constraints(solver, andrea_busy)

# Gloria's busy intervals:
#   10:00 to 11:00 -> [600, 660)
#   14:00 to 14:30 -> [840, 870)
#   16:00 to 16:30 -> [960, 990)
gloria_busy = [(600, 660), (840, 870), (960, 990)]
add_busy_constraints(solver, gloria_busy)

# Philip is free the entire day, so no constraints are added.

# Christian's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 12:00 -> [660, 720)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 15:30 -> [810, 930)
#   16:00 to 17:00 -> [960, 1020)
christian_busy = [(600, 630), (660, 720), (750, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, christian_busy)

# Denise's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 14:30 -> [750, 870)
#   15:00 to 16:00 -> [900, 960)
denise_busy = [(600, 630), (690, 720), (750, 870), (900, 960)]
add_busy_constraints(solver, denise_busy)

# Julie's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 13:30 -> [600, 810)
#   14:00 to 17:00 -> [840, 1020)
julie_busy = [(540, 570), (600, 810), (840, 1020)]
add_busy_constraints(solver, julie_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state before breaking.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")