from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define the meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to take place within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), ensure the meeting either ends before bs or starts at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Walter's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:30 to 11:00  -> [630, 660)
#   13:00 to 14:00  -> [780, 840)
walter_busy = [(540, 570), (630, 660), (780, 840)]
add_busy_constraints(solver, walter_busy)

# Jessica's busy intervals:
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 15:00 -> [870, 900)
jessica_busy = [(810, 840), (870, 900)]
add_busy_constraints(solver, jessica_busy)

# Robert's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   14:00 to 15:00 -> [840, 900)
#   16:00 to 16:30 -> [960, 990)
robert_busy = [(660, 690), (840, 900), (960, 990)]
add_busy_constraints(solver, robert_busy)

# Nicole's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 13:00  -> [690, 780)
#   13:30 to 14:30  -> [810, 870)
#   16:00 to 16:30  -> [960, 990)
nicole_busy = [(540, 570), (630, 660), (690, 780), (810, 870), (960, 990)]
add_busy_constraints(solver, nicole_busy)

# Dorothy's busy intervals:
#   9:30 to 11:30   -> [570, 690)
#   12:00 to 12:30  -> [720, 750)
#   15:00 to 16:30  -> [900, 990)
dorothy_busy = [(570, 690), (720, 750), (900, 990)]
add_busy_constraints(solver, dorothy_busy)

# Gabriel's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:00 to 12:30  -> [660, 750)
#   13:30 to 15:30  -> [810, 930)
gabriel_busy = [(540, 630), (660, 750), (810, 930)]
add_busy_constraints(solver, gabriel_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
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
    solver.pop()  # Restore the state and try the next time slot.

if not found:
    print("No valid meeting time could be found.")