from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must start and finish within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints for each participant.
# For a busy interval [bs, be) the meeting must either finish before bs or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Albert's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 14:30 -> [840, 870)
albert_busy = [(750, 780), (840, 870)]
add_busy_constraints(solver, albert_busy)

# Jean is free the entire day (no busy intervals)

# William's busy intervals:
#   10:00 to 11:00 -> [600, 660)
#   12:30 to 13:00 -> [750, 780)
#   14:30 to 16:00 -> [870, 960)
william_busy = [(600, 660), (750, 780), (870, 960)]
add_busy_constraints(solver, william_busy)

# Alan's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:00 to 13:30  -> [720, 810)
#   14:30 to 15:30  -> [870, 930)
#   16:00 to 17:00  -> [960, 1020)
alan_busy = [(570, 600), (630, 690), (720, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, alan_busy)

# Donna's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   12:00 to 13:30  -> [720, 810)
#   14:00 to 15:00  -> [840, 900)
#   16:30 to 17:00  -> [990, 1020)
donna_busy = [(540, 600), (720, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, donna_busy)

# Christina's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   16:00 to 17:00  -> [960, 1020)
christina_busy = [(540, 660), (690, 720), (750, 780), (960, 1020)]
add_busy_constraints(solver, christina_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Format the meeting time in HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")