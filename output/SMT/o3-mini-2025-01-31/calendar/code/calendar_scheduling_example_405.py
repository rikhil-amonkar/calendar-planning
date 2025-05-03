from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must either finish before a busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Emily's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
emily_busy = [(540, 570), (660, 690), (840, 870), (990, 1020)]
add_busy_constraints(solver, emily_busy)

# Brian's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
brian_busy = [(570, 600), (870, 930), (990, 1020)]
add_busy_constraints(solver, brian_busy)

# Gerald is free all day.

# Julia is free all day.

# Logan's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 14:00  -> [660, 840)
# 16:00 to 17:00  -> [960, 1020)
logan_busy = [(540, 600), (660, 840), (960, 1020)]
add_busy_constraints(solver, logan_busy)

# Judith's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:00  -> [690, 780)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
judith_busy = [(540, 660), (690, 780), (900, 930), (960, 1020)]
add_busy_constraints(solver, judith_busy)

# Michael's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 15:30  -> [780, 930)
# 16:00 to 17:00  -> [960, 1020)
michael_busy = [(540, 570), (600, 660), (690, 750), (780, 930), (960, 1020)]
add_busy_constraints(solver, michael_busy)

# Iterate over possible meeting start times to find a valid slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()         # Save the current solver state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the state
        break
    solver.pop()      # Restore if not sat

if not found:
    print("No valid meeting time could be found.")