from z3 import *

# Create the Z3 solver instance
solver = Solver()

# Meeting parameters:
# Monday work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # To avoid overlapping with a busy interval [bs, be),
        # either the meeting has to end on or before bs, or start on or after be.
        s.add(Or(start + duration <= bs, start >= be))

# Terry's busy intervals:
#   10:30 to 11:00 → [630, 660)
#   12:00 to 12:30 → [720, 750)
#   14:00 to 15:00 → [840, 900)
terry_busy = [(630, 660), (720, 750), (840, 900)]
add_busy_constraints(solver, terry_busy)

# Gloria's busy intervals:
#   9:30 to 10:30  → [570, 630)
#   11:30 to 12:00 → [690, 720)
#   14:00 to 14:30 → [840, 870)
gloria_busy = [(570, 630), (690, 720), (840, 870)]
add_busy_constraints(solver, gloria_busy)

# Julie is free the entire day.
# No busy intervals to add for Julie.

# Albert's busy intervals:
#   9:00 to 12:00   → [540, 720)
#   12:30 to 13:00  → [750, 780)
#   14:00 to 14:30  → [840, 870)
albert_busy = [(540, 720), (750, 780), (840, 870)]
add_busy_constraints(solver, albert_busy)

# Logan's busy intervals:
#   9:00 to 10:00   → [540, 600)
#   10:30 to 12:00  → [630, 720)
#   12:30 to 13:00  → [750, 780)
#   13:30 to 16:00  → [810, 960)
#   16:30 to 17:00  → [990, 1020)
logan_busy = [(540, 600), (630, 720), (750, 780), (810, 960), (990, 1020)]
add_busy_constraints(solver, logan_busy)

# Alexander's busy intervals:
#   9:30 to 11:00   → [570, 660)
#   11:30 to 13:00  → [690, 780)
#   14:30 to 15:30  → [870, 930)
alexander_busy = [(570, 660), (690, 780), (870, 930)]
add_busy_constraints(solver, alexander_busy)

# Since the group would like to meet at their earliest availability,
# we search for the smallest start time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        # Extract and print the meeting start and end times.
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state before breaking out
        break
    solver.pop()  # Restore state and try the next time slot

if not found:
    print("No valid meeting time could be found.")