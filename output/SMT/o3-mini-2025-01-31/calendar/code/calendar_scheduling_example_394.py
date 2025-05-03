from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 (540) to 17:00 (1020) and meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must either
        # finish before the interval starts or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Nicole's calendar is free the entire day, so no constraints.

# Randy's calendar is free the entire day, so no constraints.

# Michelle's busy intervals:
#   10:00 to 11:00 -> [600, 660)
michelle_busy = [(600, 660)]
add_busy_constraints(solver, michelle_busy)

# Matthew's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 13:30  -> [720, 810)
#   14:00 to 15:30  -> [840, 930)
matthew_busy = [(540, 630), (660, 690), (720, 810), (840, 930)]
add_busy_constraints(solver, matthew_busy)

# Andrea's busy intervals:
#   10:00 to 11:00  -> [600, 660)
#   11:30 to 12:00  -> [690, 720)
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 16:00  -> [870, 960)
#   16:30 to 17:00  -> [990, 1020)
andrea_busy = [(600, 660), (690, 720), (780, 810), (870, 960), (990, 1020)]
add_busy_constraints(solver, andrea_busy)

# Douglas's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 13:30 -> [630, 810)
#   14:00 to 14:30 -> [840, 870)
#   15:00 to 17:00 -> [900, 1020)
douglas_busy = [(540, 570), (630, 810), (840, 870), (900, 1020)]
add_busy_constraints(solver, douglas_busy)

# Find the earliest meeting time by iterating minute-by-minute.
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
        solver.pop()  # Restore state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")