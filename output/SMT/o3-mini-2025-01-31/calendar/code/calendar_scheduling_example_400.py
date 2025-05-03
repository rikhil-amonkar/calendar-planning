from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working day in minutes: from 9:00 (540) to 17:00 (1020)
# and meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure meeting happens within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that prevent overlapping with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must end before a busy interval begins,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Rachel is free the entire day - no constraints.

# Katherine's busy intervals:
#   10:00 to 11:00    -> [600, 660)
#   12:30 to 13:00    -> [750, 780)
#   14:00 to 15:00    -> [840, 900)
#   16:00 to 16:30    -> [960, 990)
katherine_busy = [(600, 660), (750, 780), (840, 900), (960, 990)]
add_busy_constraints(solver, katherine_busy)

# Kelly's busy intervals:
#   11:30 to 12:30    -> [690, 750)
#   13:00 to 14:30    -> [780, 870)
#   16:00 to 16:30    -> [960, 990)
kelly_busy = [(690, 750), (780, 870), (960, 990)]
add_busy_constraints(solver, kelly_busy)

# Cynthia's busy intervals:
#   13:30 to 14:00    -> [810, 840)
#   14:30 to 15:30    -> [870, 930)
#   16:00 to 16:30    -> [960, 990)
cynthia_busy = [(810, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, cynthia_busy)

# Anthony's busy intervals:
#   9:00 to 11:00     -> [540, 660)
#   12:00 to 17:00    -> [720, 1020)
anthony_busy = [(540, 660), (720, 1020)]
add_busy_constraints(solver, anthony_busy)

# Ryan's busy intervals:
#   9:00 to 11:00     -> [540, 660)
#   12:30 to 13:30    -> [750, 810)
#   14:00 to 14:30    -> [840, 870)
#   15:00 to 16:30    -> [900, 990)
ryan_busy = [(540, 660), (750, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, ryan_busy)

# Richard's busy intervals:
#   9:30 to 10:30     -> [570, 630)
#   12:00 to 13:30    -> [720, 810)
#   15:30 to 17:00    -> [930, 1020)
richard_busy = [(570, 630), (720, 810), (930, 1020)]
add_busy_constraints(solver, richard_busy)

# Try each possible start time (minute-by-minute) within the allowed window
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()           # Save the current state
    solver.add(start == t)  # Enforce a candidate start time
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()  # Restore state
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")