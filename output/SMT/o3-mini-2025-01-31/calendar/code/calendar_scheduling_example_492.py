from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within the workday.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must end at or before b_start or begin at or after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# David is free the entire day, no constraints.

# Julie is busy during:
# 11:30 to 12:00  -> [690, 720)
# 14:30 to 15:00  -> [870, 900)
julie_busy = [(690, 720), (870, 900)]
add_busy_constraints(solver, julie_busy)

# Natalie is busy during:
# 13:30 to 14:30  -> [810, 870)
natalie_busy = [(810, 870)]
add_busy_constraints(solver, natalie_busy)

# Michelle is free the entire day, no constraints.

# Brittany is busy during:
# 9:00 to 10:30   -> [540, 630)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 17:00  -> [840, 1020)
brittany_busy = [(540, 630), (690, 750), (780, 810), (840, 1020)]
add_busy_constraints(solver, brittany_busy)

# Richard is busy during:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 17:00  -> [810, 1020)
richard_busy = [(540, 660), (690, 780), (810, 1020)]
add_busy_constraints(solver, richard_busy)

# Christine is busy during:
# 9:00 to 10:30   -> [540, 630)
# 12:00 to 14:30  -> [720, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
christine_busy = [(540, 630), (720, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, christine_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")