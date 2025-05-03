from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# The meeting must be within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # To avoid overlap, the meeting should either end
        # before a busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Teresa's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:00 to 14:00 -> [720, 840)
# 16:30 to 17:00 -> [990, 1020)
teresa_busy = [(570, 600), (720, 840), (990, 1020)]
add_busy_constraints(solver, teresa_busy)

# Amanda's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 14:30 -> [840, 870)
amanda_busy = [(690, 720), (840, 870)]
add_busy_constraints(solver, amanda_busy)

# Frances is free the entire day; no busy intervals.

# Evelyn's busy intervals:
# 9:00 to 12:00 -> [540, 720)
# 12:30 to 14:00 -> [750, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
evelyn_busy = [(540, 720), (750, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, evelyn_busy)

# Betty's busy intervals:
# 9:00 to 10:00 -> [540, 600)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 15:30 -> [810, 930)
# 16:00 to 17:00 -> [960, 1020)
betty_busy = [(540, 600), (630, 690), (720, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, betty_busy)

# Try to find a valid meeting time by iterating over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore the state
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")