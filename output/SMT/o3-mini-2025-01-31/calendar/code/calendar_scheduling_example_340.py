from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(s, busy_intervals):
    # For each busy interval [bs, be), the meeting must finish at or before bs or start at or after be.
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Aaron's busy intervals:
#   10:30 to 12:00 -> [630, 720)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 15:00 -> [870, 900)
#   16:30 to 17:00 -> [990, 1020)
aaron_busy = [(630, 720), (780, 810), (870, 900), (990, 1020)]
add_busy_constraints(solver, aaron_busy)

# Frank's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 12:30 -> [720, 750)
#   14:30 to 15:30 -> [870, 930)
#   16:30 to 17:00 -> [990, 1020)
frank_busy = [(540, 570), (660, 690), (720, 750), (870, 930), (990, 1020)]
add_busy_constraints(solver, frank_busy)

# Diane's busy intervals:
#   9:00 to 10:00 -> [540, 600)
diane_busy = [(540, 600)]
add_busy_constraints(solver, diane_busy)

# Dylan's busy intervals:
#   9:30 to 10:30 -> [570, 630)
#   12:00 to 15:00 -> [720, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
dylan_busy = [(570, 630), (720, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, dylan_busy)

# Alexis's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 15:00 -> [810, 900)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
alexis_busy = [(540, 570), (630, 660), (750, 780), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, alexis_busy)

# Mason's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 14:30  -> [750, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:30 to 17:00  -> [990, 1020)
mason_busy = [(540, 600), (630, 690), (750, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, mason_busy)

# Find the earliest valid meeting time within the allowed time range.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state
        break
    solver.pop()  # Restore state and try next potential start time

if not found:
    print("No valid meeting time could be found.")