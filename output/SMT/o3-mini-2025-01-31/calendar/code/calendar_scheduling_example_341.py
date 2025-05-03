from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(s, busy_intervals):
    # For each busy interval [bs, be),
    # ensure that the meeting either finishes before the interval (start+duration <= bs)
    # or starts after the interval (start >= be).
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Ruth's busy intervals:
#   9:30 to 11:00 → [570, 660)
#   13:00 to 14:00 → [780, 840)
#   15:00 to 15:30 → [900, 930)
ruth_busy = [(570, 660), (780, 840), (900, 930)]
add_busy_constraints(solver, ruth_busy)

# Aaron's busy intervals:
#   10:00 to 10:30 → [600, 630)
#   11:00 to 12:00 → [660, 720)
#   12:30 to 13:30 → [750, 810)
#   15:00 to 15:30 → [900, 930)
aaron_busy = [(600, 630), (660, 720), (750, 810), (900, 930)]
add_busy_constraints(solver, aaron_busy)

# Brittany's busy intervals:
#   13:00 to 13:30 → [780, 810)
#   14:30 to 15:00 → [870, 900)
brittany_busy = [(780, 810), (870, 900)]
add_busy_constraints(solver, brittany_busy)

# Jeffrey's busy intervals:
#   9:00 to 10:30  → [540, 630)
#   11:00 to 12:00 → [660, 720)
#   13:00 to 16:30 → [780, 990)
jeffrey_busy = [(540, 630), (660, 720), (780, 990)]
add_busy_constraints(solver, jeffrey_busy)

# Virginia's busy intervals:
#   9:00 to 16:00 → [540, 960)
virginia_busy = [(540, 960)]
add_busy_constraints(solver, virginia_busy)

# Peter's busy intervals:
#   9:00 to 12:30  → [540, 750)
#   13:00 to 14:00 → [780, 840)
#   14:30 to 15:00 → [870, 900)
#   15:30 to 16:30 → [930, 990)
peter_busy = [(540, 750), (780, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, peter_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the solver state and exit.
        break
    solver.pop()  # Restore state and try the next potential start time.

if not found:
    print("No valid meeting time could be found.")