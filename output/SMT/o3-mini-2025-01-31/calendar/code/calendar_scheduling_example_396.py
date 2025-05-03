from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 (540) to 17:00 (1020)
# and meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must finish before bs or start at/after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Andrea's calendar is free the entire day, so no constraints.

# Jack's busy intervals:
#  9:00 to 9:30   -> [540, 570)
#  14:00 to 14:30 -> [840, 870)
jack_busy = [(540, 570), (840, 870)]
add_busy_constraints(solver, jack_busy)

# Madison's busy intervals:
#  9:30 to 10:30  -> [570, 630)
#  13:00 to 14:00  -> [780, 840)
#  15:00 to 15:30  -> [900, 930)
#  16:30 to 17:00  -> [990, 1020)
madison_busy = [(570, 630), (780, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, madison_busy)

# Rachel's busy intervals:
#  9:30 to 10:30  -> [570, 630)
#  11:00 to 11:30 -> [660, 690)
#  12:00 to 13:30 -> [720, 810)
#  14:30 to 15:30 -> [870, 930)
#  16:00 to 17:00 -> [960, 1020)
rachel_busy = [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, rachel_busy)

# Douglas's busy intervals:
#  9:00 to 11:30  -> [540, 690)
#  12:00 to 16:30 -> [720, 990)
douglas_busy = [(540, 690), (720, 990)]
add_busy_constraints(solver, douglas_busy)

# Ryan's busy intervals:
#  9:00 to 9:30   -> [540, 570)
#  13:00 to 14:00 -> [780, 840)
#  14:30 to 17:00 -> [870, 1020)
ryan_busy = [(540, 570), (780, 840), (870, 1020)]
add_busy_constraints(solver, ryan_busy)

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