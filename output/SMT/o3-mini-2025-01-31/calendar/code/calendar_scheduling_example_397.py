from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 (540) to 17:00 (1020)
# and the meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must finish before bs
        # or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Jonathan is free all day, so no constraints.

# Matthew's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 16:30 -> [960, 990)
matthew_busy = [(600, 630), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, matthew_busy)

# Carl's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   13:30 to 14:00 -> [810, 840)
carl_busy = [(570, 600), (810, 840)]
add_busy_constraints(solver, carl_busy)

# Ryan's busy intervals:
#   9:30 to 11:00  -> [570, 660)
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 16:00 -> [900, 960)
ryan_busy = [(570, 660), (690, 750), (780, 810), (900, 960)]
add_busy_constraints(solver, ryan_busy)

# Albert's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 12:30 -> [600, 750)
#   13:00 to 15:30 -> [780, 930)
#   16:00 to 16:30 -> [960, 990)
albert_busy = [(540, 570), (600, 750), (780, 930), (960, 990)]
add_busy_constraints(solver, albert_busy)

# Danielle's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 14:30  -> [750, 870)
#   15:00 to 15:30  -> [900, 930)
danielle_busy = [(540, 570), (630, 690), (750, 870), (900, 930)]
add_busy_constraints(solver, danielle_busy)

# Iterate over possible start times minute-by-minute to find the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")