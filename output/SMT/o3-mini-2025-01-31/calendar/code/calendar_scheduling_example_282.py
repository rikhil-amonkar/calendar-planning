from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain the meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints such that the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting does not overlap busy interval if it finishes before it starts or starts after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Larry's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
larry_busy = [(630, 660), (690, 720)]
add_busy_constraints(solver, larry_busy)

# Juan and Emily are free the entire day - no constraints needed for them.

# Joan's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 14:00  -> [750, 840)
# 15:00 to 15:30  -> [900, 930)
joan_busy = [(570, 660), (690, 720), (750, 840), (900, 930)]
add_busy_constraints(solver, joan_busy)

# Julie's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:30 to 17:00  -> [750, 1020)
julie_busy = [(540, 690), (750, 1020)]
add_busy_constraints(solver, julie_busy)

# Search for a valid meeting start time.
valid_time_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        valid_time_found = True
        solver.pop()  # Restore state before breaking.
        break
    solver.pop()

if not valid_time_found:
    print("No valid meeting time could be found.")