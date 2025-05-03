from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval [bs, be),
# ensure the meeting [start, start+duration) does not overlap with it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must finish on or before a busy interval starts,
        # or start on or after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Patrick's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
patrick_busy = [(540, 570), (600, 630), (810, 840), (960, 990)]
add_busy_constraints(solver, patrick_busy)

# Kayla's busy intervals:
# 12:30 to 13:30 -> [750, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
kayla_busy = [(750, 810), (900, 930), (960, 990)]
add_busy_constraints(solver, kayla_busy)

# Carl's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 17:00 -> [870, 1020)
carl_busy = [(630, 660), (720, 750), (780, 810), (870, 1020)]
add_busy_constraints(solver, carl_busy)

# Christian's busy intervals:
# 9:00 to 12:30 -> [540, 750)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 17:00 -> [870, 1020)
christian_busy = [(540, 750), (780, 840), (870, 1020)]
add_busy_constraints(solver, christian_busy)

# Search for the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state before breaking.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")