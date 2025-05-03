from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Vincent prefers not to have meetings after 12:30.
# So the meeting must be scheduled so that it finishes by 12:30 (750 minutes).
solver.add(start + duration <= 750)

# Define a helper function to ensure the meeting does not intersect with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Austin's calendar is wide open - no constraints are needed.

# Vincent's busy intervals:
# 9:00 to 10:30 -> [540, 630)
# 12:00 to 15:00 -> [720, 900)
# 15:30 to 17:00 -> [930, 1020)
vincent_busy = [(540, 630), (720, 900), (930, 1020)]
add_busy_constraints(solver, vincent_busy)

# Now, search for the earliest valid 30-minute meeting time.
found = False
# Because meeting must finish by 750, the latest start time is 750 - duration = 720.
for t in range(540, 720 + 1):
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