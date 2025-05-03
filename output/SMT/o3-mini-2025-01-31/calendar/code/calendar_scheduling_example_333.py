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
        # To ensure the meeting does not overlap a busy interval [bs, be),
        # it must either finish before the busy interval starts or start after it ends.
        s.add(Or(start + duration <= bs, start >= be))

# Debra's busy interval:
#   15:00 to 16:00 → [900, 960)
debra_busy = [(900, 960)]
add_busy_constraints(solver, debra_busy)

# Sean's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   12:00 to 12:30 → [720, 750)
#   13:00 to 14:00 → [780, 840)
#   14:30 to 15:00 → [870, 900)
#   16:30 to 17:00 → [990, 1020)
sean_busy = [(540, 570), (720, 750), (780, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, sean_busy)

# Randy's busy intervals:
#   11:00 to 12:00 → [660, 720)
#   13:00 to 14:00 → [780, 840)
#   15:00 to 15:30 → [900, 930)
#   16:30 to 17:00 → [990, 1020)
randy_busy = [(660, 720), (780, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, randy_busy)

# Gary's busy intervals:
#   9:30 to 11:00  → [570, 660)
#   11:30 to 13:00 → [690, 780)
#   14:00 to 15:30 → [840, 930)
#   16:30 to 17:00 → [990, 1020)
gary_busy = [(570, 660), (690, 780), (840, 930), (990, 1020)]
add_busy_constraints(solver, gary_busy)

# Joseph's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:30 to 11:00 → [630, 660)
#   11:30 to 12:00 → [690, 720)
#   12:30 to 13:00 → [750, 780)
#   13:30 to 14:00 → [810, 840)
#   15:00 to 16:00 → [900, 960)
#   16:30 to 17:00 → [990, 1020)
joseph_busy = [(540, 570), (630, 660), (690, 720), (750, 780), (810, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, joseph_busy)

# Christina's busy intervals:
#   9:00 to 10:00  → [540, 600)
#   10:30 to 12:30 → [630, 750)
#   14:00 to 16:00 → [840, 960)
christina_busy = [(540, 600), (630, 750), (840, 960)]
add_busy_constraints(solver, christina_busy)

# Find the earliest valid meeting time.
found = False
# The meeting can start anytime between 9:00 (540) and 16:30 (990) inclusive.
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")