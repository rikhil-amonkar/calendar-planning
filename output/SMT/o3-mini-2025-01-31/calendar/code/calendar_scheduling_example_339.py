from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Monday work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must either finish on or before bs or start on or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Zachary is free all day, so no constraints.

# Kenneth's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:30 to 12:00  -> [690, 720)
#   14:30 to 15:30  -> [870, 930)
#   16:00 to 16:30  -> [960, 990)
kenneth_busy = [(540, 600), (690, 720), (870, 930), (960, 990)]
add_busy_constraints(solver, kenneth_busy)

# Judy's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   16:00 to 16:30  -> [960, 990)
judy_busy = [(570, 600), (960, 990)]
add_busy_constraints(solver, judy_busy)

# Jean's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:30  -> [690, 750)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 16:00  -> [870, 960)
#   16:30 to 17:00  -> [990, 1020)
jean_busy = [(540, 600), (630, 660), (690, 750), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, jean_busy)

# Sean's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:30 to 14:30  -> [690, 870)
#   15:00 to 16:00  -> [900, 960)
sean_busy = [(570, 630), (690, 870), (900, 960)]
add_busy_constraints(solver, sean_busy)

# Alice's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:30  -> [750, 810)
#   14:00 to 16:00  -> [840, 960)
#   16:30 to 17:00  -> [990, 1020)
alice_busy = [(540, 570), (630, 660), (690, 720), (750, 810), (840, 960), (990, 1020)]
add_busy_constraints(solver, alice_busy)

# Find the earliest valid meeting time.
found = False

for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the state before breaking.
        break
    solver.pop()  # Restore before trying the next time slot.

if not found:
    print("No valid meeting time could be found.")