from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Willie does not want to meet before 10:00, so we enforce:
solver.add(start >= 600)

# Also, the meeting must end by 17:00.
solver.add(start + duration <= 1020)

# Helper function to add busy interval constraints.
# For a busy interval [bs, be), the meeting must either finish before bs or start after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Willie's calendar is wide open (apart from the preference constraint).
# Paul's calendar is wide open.
# Kenneth's calendar is wide open.

# Dennis's busy intervals:
#   9:30  to 12:30  -> [570, 750)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 15:00  -> [840, 900)
#   15:30 to 17:00  -> [930, 1020)
dennis_busy = [(570, 750), (780, 810), (840, 900), (930, 1020)]
add_busy_constraints(solver, dennis_busy)

# Elijah's busy intervals:
#   10:30 to 12:30 -> [630, 750)
#   14:00 to 15:30 -> [840, 930)
#   16:30 to 17:00 -> [990, 1020)
elijah_busy = [(630, 750), (840, 930), (990, 1020)]
add_busy_constraints(solver, elijah_busy)

# Christian's busy intervals:
#   9:30  to 10:30 -> [570, 630)
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 15:30 -> [780, 930)
#   16:30 to 17:00 -> [990, 1020)
christian_busy = [(570, 630), (690, 750), (780, 930), (990, 1020)]
add_busy_constraints(solver, christian_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(600, 1020 - duration + 1):  # starting at 10:00 due to Willie's constraint
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")