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

# Helper function: for each busy interval [bs, be), 
# ensure the meeting either finishes by bs or starts at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jeffrey's busy intervals:
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 17:00 -> [960,1020)
jeffrey_busy = [(840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, jeffrey_busy)

# Benjamin's busy intervals:
#   9:00 to 9:30  -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
benjamin_busy = [(540, 570), (600, 630)]
add_busy_constraints(solver, benjamin_busy)

# Denise's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   15:00 to 15:30 -> [900, 930)
denise_busy = [(570, 600), (900, 930)]
add_busy_constraints(solver, denise_busy)

# Alexis's busy intervals:
#   9:00 to 11:30   -> [540, 690)
#   12:30 to 14:30  -> [750, 870)
#   16:00 to 16:30  -> [960, 990)
alexis_busy = [(540, 690), (750, 870), (960, 990)]
add_busy_constraints(solver, alexis_busy)

# Shirley's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 12:00 -> [660, 720)
#   12:30 to 14:00 -> [750, 840)
#   15:00 to 17:00 -> [900, 1020)
shirley_busy = [(540, 630), (660, 720), (750, 840), (900, 1020)]
add_busy_constraints(solver, shirley_busy)

# Philip's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 13:30 -> [780, 810)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 17:00 -> [960, 1020)
philip_busy = [(540, 570), (630, 660), (720, 750), (780, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, philip_busy)

# Iterate over possible start times to find a valid meeting time.
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