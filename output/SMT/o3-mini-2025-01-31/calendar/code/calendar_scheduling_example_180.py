from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
# Basic work hours constraint.
solver.add(start >= 540, start + duration <= 1020)
# Natalie's preference: she would rather not meet after 10:30.
# So we force the meeting to finish by 10:30.
solver.add(start + duration <= 630)

# Helper function:
# Adds a constraint that the meeting interval [start, start+duration)
# does not overlap with any busy interval [busy_start, busy_end).
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# David's busy intervals:
#   14:00 to 14:30  -> [840, 870)
#   16:30 to 17:00  -> [990, 1020)
david_busy = [(840, 870), (990, 1020)]
add_busy_constraints(solver, david_busy)

# Ethan's busy intervals:
#   13:00 to 13:30  -> [780, 810)
#   14:30 to 15:00  -> [870, 900)
ethan_busy = [(780, 810), (870, 900)]
add_busy_constraints(solver, ethan_busy)

# Bradley's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 12:00  -> [660, 720)
#   13:30 to 14:00  -> [810, 840)
#   15:30 to 17:00  -> [930, 1020)
bradley_busy = [(570, 630), (660, 720), (810, 840), (930, 1020)]
add_busy_constraints(solver, bradley_busy)

# Natalie's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   10:30 to 12:00  -> [630, 720)
#   12:30 to 15:30  -> [750, 930)
#   16:00 to 17:00  -> [960, 1020)
natalie_busy = [(570, 600), (630, 720), (750, 930), (960, 1020)]
add_busy_constraints(solver, natalie_busy)

# Find the earliest valid meeting start time.
solution_found = False
# Because Natalie's constraint forces meeting finish by 10:30 (630),
# the meeting must start no later than 600.
for t in range(540, 601):  # 540 = 9:00, 600 = 10:00
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")