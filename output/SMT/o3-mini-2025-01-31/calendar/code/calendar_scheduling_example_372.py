from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# The meeting must be scheduled within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval [bs, be), the meeting must finish at or before bs or begin at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Barbara's busy intervals:
#   10:30 to 11:30 -> [630, 690)
#   14:00 to 14:30 -> [840, 870)
#   16:00 to 16:30 -> [960, 990)
barbara_busy = [(630, 690), (840, 870), (960, 990)]
add_busy_constraints(solver, barbara_busy)

# Arthur's busy intervals:
#   11:30 to 13:00 -> [690, 780)
#   13:30 to 14:00 -> [810, 840)
arthur_busy = [(690, 780), (810, 840)]
add_busy_constraints(solver, arthur_busy)

# Elijah's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 11:00  -> [630, 660)
#   12:00 to 12:30  -> [720, 750)
#   14:00 to 15:30  -> [840, 930)
elijah_busy = [(570, 600), (630, 660), (720, 750), (840, 930)]
add_busy_constraints(solver, elijah_busy)

# Natalie's busy intervals:
#   9:00 to 13:00   -> [540, 780)
#   13:30 to 14:30  -> [810, 870)
#   15:00 to 17:00  -> [900, 1020)
natalie_busy = [(540, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, natalie_busy)

# Philip's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   11:00 to 12:00  -> [660, 720)
#   13:30 to 15:30  -> [810, 930)
#   16:30 to 17:00  -> [990, 1020)
philip_busy = [(570, 600), (660, 720), (810, 930), (990, 1020)]
add_busy_constraints(solver, philip_busy)

# Jordan's busy intervals:
#   9:00 to 13:00   -> [540, 780)
#   13:30 to 15:30  -> [810, 930)
#   16:00 to 17:00  -> [960, 1020)
jordan_busy = [(540, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, jordan_busy)

# Iterate over possible start times (minute by minute) and check for a valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")