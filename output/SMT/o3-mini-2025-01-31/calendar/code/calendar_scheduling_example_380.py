from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish before bs or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Adam: free all day, no busy intervals.

# Jacqueline's busy intervals:
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 13:00 -> [720, 780)
#   15:30 to 16:30 -> [930, 990)
jacqueline_busy = [(600, 660), (720, 780), (930, 990)]
add_busy_constraints(solver, jacqueline_busy)

# Denise's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:00 to 11:30 -> [660, 690)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 16:30 -> [960, 990)
denise_busy = [(570, 630), (660, 690), (810, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, denise_busy)

# Kimberly's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:00 to 13:00 -> [660, 780)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 16:30 -> [930, 990)
kimberly_busy = [(570, 630), (660, 780), (840, 900), (930, 990)]
add_busy_constraints(solver, kimberly_busy)

# Ann's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:30 -> [750, 810)
#   14:00 to 16:00 -> [840, 960)
#   16:30 to 17:00 -> [990, 1020)
ann_busy = [(570, 630), (690, 720), (750, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, ann_busy)

# Steven's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 14:30 -> [780, 870)
#   16:00 to 16:30 -> [960, 990)
steven_busy = [(570, 630), (690, 750), (780, 870), (960, 990)]
add_busy_constraints(solver, steven_busy)

# Find a meeting time by iterating over possible starting times minute-by-minute.
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