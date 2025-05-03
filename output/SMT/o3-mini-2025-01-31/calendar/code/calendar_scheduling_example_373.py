from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for a list of busy intervals [bs, be), enforce that the meeting 
# does not overlap by stating that it either ends by bs or starts at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Julia: wide open all day; no constraints.

# Joseph's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 12:30 -> [720, 750)
joseph_busy = [(540, 570), (600, 660), (720, 750)]
add_busy_constraints(solver, joseph_busy)

# Donna's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 16:00  -> [840, 960)
donna_busy = [(570, 600), (750, 780), (840, 960)]
add_busy_constraints(solver, donna_busy)

# Bruce's busy intervals:
#   9:30 to 11:00   -> [570, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 14:00  -> [750, 840)
#   15:00 to 16:30  -> [900, 990)
bruce_busy = [(570, 660), (690, 720), (750, 840), (900, 990)]
add_busy_constraints(solver, bruce_busy)

# Bobby's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 15:30  -> [840, 930)
#   16:00 to 16:30  -> [960, 990)
bobby_busy = [(540, 570), (630, 690), (750, 780), (840, 930), (960, 990)]
add_busy_constraints(solver, bobby_busy)

# Arthur's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 10:30  -> [600, 630)
#   11:30 to 12:00  -> [690, 720)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 16:30  -> [900, 990)
arthur_busy = [(540, 570), (600, 630), (690, 720), (780, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, arthur_busy)

# Now, we iterate over possible start times (minute by minute within the allowed timeframe)
# checking for a valid meeting time that satisfies all constraints.
found = False
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