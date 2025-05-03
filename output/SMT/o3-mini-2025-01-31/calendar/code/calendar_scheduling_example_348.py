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
# For a busy interval [bs, be), the meeting must either finish before bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Anna's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   12:30 to 13:00 -> [750, 780)
#   15:00 to 16:00 -> [900, 960)
anna_busy = [(630, 660), (750, 780), (900, 960)]
add_busy_constraints(solver, anna_busy)

# Nathan has no meetings the whole day (free).

# Benjamin's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 14:30 -> [840, 870)
benjamin_busy = [(600, 630), (660, 690), (750, 780), (840, 870)]
add_busy_constraints(solver, benjamin_busy)

# Noah's busy intervals:
#   9:30 to 13:30   -> [570, 810)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
noah_busy = [(570, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, noah_busy)

# Bruce's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 13:00  -> [660, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 17:00  -> [870, 1020)
bruce_busy = [(570, 630), (660, 780), (810, 840), (870, 1020)]
add_busy_constraints(solver, bruce_busy)

# Matthew's busy intervals:
#   9:30 to 16:30   -> [570, 990)
matthew_busy = [(570, 990)]
add_busy_constraints(solver, matthew_busy)

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
        solver.pop()  # Restore the solver state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")