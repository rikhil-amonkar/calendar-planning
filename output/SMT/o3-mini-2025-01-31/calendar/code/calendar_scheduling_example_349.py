from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to take place within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting must either end before bs or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Carl's busy intervals:
#   10:00 to 11:30 -> [600, 690)
#   15:00 to 15:30 -> [900, 930)
carl_busy = [(600, 690), (900, 930)]
add_busy_constraints(solver, carl_busy)

# Patricia is free the entire day (no busy intervals).

# Madison's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
madison_busy = [(690, 720), (750, 780)]
add_busy_constraints(solver, madison_busy)

# Gloria's busy intervals:
#   10:00 to 12:00 -> [600, 720)
#   13:00 to 13:30 -> [780, 810)
#   14:00 to 15:00 -> [840, 900)
#   16:00 to 16:30 -> [960, 990)
gloria_busy = [(600, 720), (780, 810), (840, 900), (960, 990)]
add_busy_constraints(solver, gloria_busy)

# Kenneth's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:30 to 12:00  -> [690, 720)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
kenneth_busy = [(540, 600), (690, 720), (780, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, kenneth_busy)

# Betty's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 14:30  -> [780, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
betty_busy = [(570, 600), (630, 690), (720, 750), (780, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, betty_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the state before breaking.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")