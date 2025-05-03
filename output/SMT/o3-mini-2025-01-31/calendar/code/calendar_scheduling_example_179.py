from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure the meeting interval [start, start+duration)
# does not overlap a busy interval [bs, be)
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Joseph's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 15:00 to 15:30 -> [900, 930)
joseph_busy = [(720, 750), (900, 930)]
add_busy_constraints(solver, joseph_busy)

# Laura's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 14:00 to 14:30 -> [840, 870)
laura_busy = [(570, 600), (840, 870)]
add_busy_constraints(solver, laura_busy)

# Jeffrey's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:00 -> [870, 960)
jeffrey_busy = [(540, 570), (600, 630), (660, 690),
                (720, 750), (810, 840), (870, 960)]
add_busy_constraints(solver, jeffrey_busy)

# Jeremy's busy intervals:
# 9:30 to 12:30 -> [570, 750)
# 13:00 to 17:00 -> [780, 1020)
jeremy_busy = [(570, 750), (780, 1020)]
add_busy_constraints(solver, jeremy_busy)

# Try to find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore state before breaking.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")