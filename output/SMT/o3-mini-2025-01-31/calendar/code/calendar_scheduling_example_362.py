from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Regular work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
# However, Dorothy would like to avoid meetings after 15:00, so we require the meeting to finish by 15:00 (900 minutes).
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be within work hours and finish by 15:00 (Dorothy's preference).
solver.add(start >= 540, start + duration <= 1020, start + duration <= 900)

# Helper function: for each busy interval [bs, be), ensure the meeting
# either finishes at or before the busy interval or starts at or after it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Megan's busy intervals:
# - 13:30 to 14:00: [810, 840)
# - 14:30 to 15:00: [870, 900)
megan_busy = [(810, 840), (870, 900)]
add_busy_constraints(solver, megan_busy)

# Jeremy is free all day (no busy intervals).

# Sean's busy intervals:
# - 11:00 to 11:30: [660, 690)
# - 12:00 to 12:30: [720, 750)
# - 13:30 to 14:00: [810, 840)
# - 16:00 to 16:30: [960, 990) [Note: This is after 15:00, but our meeting will be scheduled to finish by 15:00]
sean_busy = [(660, 690), (720, 750), (810, 840), (960, 990)]
add_busy_constraints(solver, sean_busy)

# Dorothy's busy intervals:
# - 9:00 to 10:00: [540, 600)
# - 11:00 to 11:30: [660, 690)
# - 12:00 to 13:00: [720, 780)
# - 14:00 to 15:30: [840, 930)
# - 16:00 to 17:00: [960, 1020)
dorothy_busy = [(540, 600), (660, 690), (720, 780), (840, 930), (960, 1020)]
add_busy_constraints(solver, dorothy_busy)

# Michael's busy intervals:
# - 9:30 to 10:00: [570, 600)
# - 10:30 to 11:30: [630, 690)
# - 12:30 to 13:00: [750, 780)
# - 13:30 to 14:30: [810, 870)
# - 15:00 to 15:30: [900, 930)
# - 16:00 to 16:30: [960, 990)
michael_busy = [(570, 600), (630, 690), (750, 780), (810, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, michael_busy)

# Jesse's busy intervals:
# - 10:00 to 12:30: [600, 750)
# - 14:00 to 14:30: [840, 870)
# - 16:00 to 17:00: [960, 1020)
jesse_busy = [(600, 750), (840, 870), (960, 1020)]
add_busy_constraints(solver, jesse_busy)

# Now, we search for a valid meeting start time within the allowed interval.
found = False
for t in range(540, 900 - duration + 1):  # meeting must finish by 900, so start <= 900 - duration
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