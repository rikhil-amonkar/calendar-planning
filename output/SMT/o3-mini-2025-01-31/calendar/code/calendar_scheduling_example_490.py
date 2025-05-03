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
        # The meeting [start, start+duration) must not overlap the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Nancy's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
nancy_busy = [(540, 570), (720, 750), (810, 840), (870, 900)]
add_busy_constraints(solver, nancy_busy)

# Julie is free the entire day, no constraints needed.

# Randy's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 13:30  -> [780, 810)
randy_busy = [(690, 720), (780, 810)]
add_busy_constraints(solver, randy_busy)

# Anthony's busy intervals:
# 12:00 to 12:30  -> [720, 750)
# 16:30 to 17:00  -> [990, 1020)
anthony_busy = [(720, 750), (990, 1020)]
add_busy_constraints(solver, anthony_busy)

# Alan's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:30 to 16:30  -> [930, 990)
alan_busy = [(540, 570), (600, 660), (720, 780), (810, 840), (930, 990)]
add_busy_constraints(solver, alan_busy)

# Denise's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 11:30 to 14:30  -> [690, 870)
# 15:30 to 17:00  -> [930, 1020)
denise_busy = [(540, 570), (600, 660), (690, 870), (930, 1020)]
add_busy_constraints(solver, denise_busy)

# Jacob's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 12:30  -> [660, 750)
# 13:30 to 14:30  -> [810, 870)
# 16:30 to 17:00  -> [990, 1020)
jacob_busy = [(540, 600), (660, 750), (810, 870), (990, 1020)]
add_busy_constraints(solver, jacob_busy)

# Search for the earliest valid 30-minute meeting time.
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