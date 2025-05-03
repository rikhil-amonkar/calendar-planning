from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # To ensure the meeting does not overlap with a busy interval [bs, be),
        # the meeting must finish on or before the busy interval starts or start after it ends.
        s.add(Or(start + duration <= bs, start >= be))

# Albert is free the entire day, so no constraints needed.

# Laura's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 11:00  → [600, 660)
#   15:30 to 16:00  → [930, 960)
laura_busy = [(540, 570), (600, 660), (930, 960)]
add_busy_constraints(solver, laura_busy)

# Elijah's busy intervals:
#   10:00 to 11:00  → [600, 660)
#   13:00 to 13:30  → [780, 810)
#   16:00 to 16:30  → [960, 990)
elijah_busy = [(600, 660), (780, 810), (960, 990)]
add_busy_constraints(solver, elijah_busy)

# Kenneth's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 11:30  → [600, 690)
#   12:30 to 13:00  → [750, 780)
#   13:30 to 14:00  → [810, 840)
#   16:00 to 17:00  → [960, 1020)
kenneth_busy = [(540, 570), (600, 690), (750, 780), (810, 840), (960, 1020)]
add_busy_constraints(solver, kenneth_busy)

# Adam's busy intervals:
#   9:00 to 9:30    → [540, 570)
#   10:00 to 11:00   → [600, 660)
#   12:30 to 14:30   → [750, 870)
#   15:00 to 16:00   → [900, 960)
#   16:30 to 17:00   → [990, 1020)
adam_busy = [(540, 570), (600, 660), (750, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, adam_busy)

# Heather's busy intervals:
#   10:00 to 11:30   → [600, 690)
#   13:30 to 15:00   → [810, 900)
#   16:00 to 17:00   → [960, 1020)
heather_busy = [(600, 690), (810, 900), (960, 1020)]
add_busy_constraints(solver, heather_busy)

# The group prefers to meet at their earliest availability.
# We search for the smallest meeting start time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
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