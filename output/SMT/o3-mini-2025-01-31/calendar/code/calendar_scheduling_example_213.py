from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlapping constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either finish before the busy interval starts or start after it ends.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jeremy's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
jeremy_busy = [(540, 570), (660, 690), (810, 840), (900, 930)]
add_busy_constraints(solver, jeremy_busy)

# Diana is free the entire day, so no additional constraints.

# Beverly is free the entire day, so no additional constraints.

# Diane's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 17:00 -> [930, 1020)
diane_busy = [(540, 570), (600, 630), (750, 810), (840, 870), (930, 1020)]
add_busy_constraints(solver, diane_busy)

# Megan's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 16:30  -> [840, 990)
megan_busy = [(540, 600), (630, 690), (750, 780), (840, 990)]
add_busy_constraints(solver, megan_busy)

# Search for the earliest meeting time that satisfies all constraints.
solution_found = False
# The latest possible meeting start is 1020 - duration = 960.
for t in range(540, 961):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")