from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy-time constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either end at or before b_start,
        # or start at or after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Cynthia's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
cynthia_busy = [(690, 720), (750, 780), (840, 870), (900, 930)]
add_busy_constraints(solver, cynthia_busy)

# Carol's busy intervals:
# 9:00 to 10:00 -> [540, 600)
carol_busy = [(540, 600)]
add_busy_constraints(solver, carol_busy)

# Jean is free the entire day, so no constraints.

# Billy's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
billy_busy = [(540, 570), (600, 630)]
add_busy_constraints(solver, billy_busy)

# Albert's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 13:00   -> [690, 780)
# 14:00 to 15:30   -> [840, 930)
# 16:30 to 17:00   -> [990, 1020)
albert_busy = [(570, 600), (690, 780), (840, 930), (990, 1020)]
add_busy_constraints(solver, albert_busy)

# Doris's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 16:30  -> [960, 990)
doris_busy = [(540, 690), (720, 780), (810, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, doris_busy)

# Keith's busy intervals:
# 10:00 to 10:30   -> [600, 630)
# 11:00 to 12:00   -> [660, 720)
# 12:30 to 14:00   -> [750, 840)
# 15:00 to 15:30   -> [900, 930)
# 16:00 to 16:30   -> [960, 990)
keith_busy = [(600, 630), (660, 720), (750, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, keith_busy)

# Find the earliest valid meeting time by iterating over possible start times.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        valid_start = t
        valid_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(valid_start, 60)
        eh, em = divmod(valid_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")