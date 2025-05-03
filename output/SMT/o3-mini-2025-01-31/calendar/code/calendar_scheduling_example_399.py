from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: from 9:00 (540) to 17:00 (1020)
# and meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Ensure the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting must not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For a busy interval [bs, be), the meeting must either finish before bs
        # or begin at/after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Andrew's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   15:30 to 16:00 -> [930, 960)
andrew_busy = [(660, 690), (930, 960)]
add_busy_constraints(solver, andrew_busy)

# Sandra is free the entire day, so no constraints.

# Lawrence's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   11:30 to 12:00 -> [690, 720)
lawrence_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, lawrence_busy)

# Olivia's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 12:00  -> [660, 720)
#   12:30 to 13:30  -> [750, 810)
#   14:30 to 15:00  -> [870, 900)
#   16:00 to 16:30  -> [960, 990)
olivia_busy = [(540, 600), (660, 720), (750, 810), (870, 900), (960, 990)]
add_busy_constraints(solver, olivia_busy)

# Bruce's busy intervals:
#   9:00 to 11:30   -> [540, 690)
#   12:00 to 13:00  -> [720, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 16:30  -> [870, 990)
bruce_busy = [(540, 690), (720, 780), (810, 840), (870, 990)]
add_busy_constraints(solver, bruce_busy)

# Joyce's busy intervals:
#   9:30 to 12:30   -> [570, 750)
#   13:30 to 14:30  -> [810, 870)
#   15:30 to 16:30  -> [930, 990)
joyce_busy = [(570, 750), (810, 870), (930, 990)]
add_busy_constraints(solver, joyce_busy)

# Now, iterate over possible start times (minute by minute) to find the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()         # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()   # Restore the state.
        break
    solver.pop()       # Restore state if this candidate did not work.

if not found:
    print("No valid meeting time could be found.")