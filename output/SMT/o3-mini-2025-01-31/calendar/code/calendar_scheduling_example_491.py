from z3 import Solver, Int, Or, sat

# Create the Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy-time constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # To avoid overlapping with a busy interval [b_start, b_end),
        # the meeting must finish at or before b_start or start after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Patricia's busy intervals:
# 12:00 to 13:00  -> [720, 780)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
patricia_busy = [(720, 780), (840, 870), (900, 930)]
add_busy_constraints(solver, patricia_busy)

# Nathan's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 14:00 to 15:00  -> [840, 900)
# 16:00 to 16:30  -> [960, 990)
nathan_busy = [(690, 720), (840, 900), (960, 990)]
add_busy_constraints(solver, nathan_busy)

# James's busy intervals:
# 12:30 to 13:00  -> [750, 780)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 17:00  -> [960, 1020)
james_busy = [(750, 780), (870, 900), (960, 1020)]
add_busy_constraints(solver, james_busy)

# Pamela's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 10:30  -> [600, 630)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 14:30  -> [840, 870)
# 16:00 to 17:00  -> [960, 1020)
pamela_busy = [(540, 570), (600, 630), (750, 780), (840, 870), (960, 1020)]
add_busy_constraints(solver, pamela_busy)

# Raymond's busy intervals:
# 9:00 to 13:00   -> [540, 780)
# 13:30 to 16:00  -> [810, 960)
# 16:30 to 17:00  -> [990, 1020)
raymond_busy = [(540, 780), (810, 960), (990, 1020)]
add_busy_constraints(solver, raymond_busy)

# Cheryl's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 12:30  -> [600, 750)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
cheryl_busy = [(540, 570), (600, 750), (870, 900), (930, 960)]
add_busy_constraints(solver, cheryl_busy)

# Michelle's busy intervals:
# 9:00 to 11:00    -> [540, 660)
# 11:30 to 12:00   -> [690, 720)
# 12:30 to 13:00   -> [750, 780)
# 14:30 to 15:00   -> [870, 900)
# 15:30 to 17:00   -> [930, 1020)
michelle_busy = [(540, 660), (690, 720), (750, 780), (870, 900), (930, 1020)]
add_busy_constraints(solver, michelle_busy)

# Look for the earliest valid 30-minute meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")