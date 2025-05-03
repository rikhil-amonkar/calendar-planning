from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 60  # meeting duration in minutes (one hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Jose cannot meet on Monday after 10:30.
# Therefore, the meeting must finish by 10:30 (630 minutes).
solver.add(start + duration <= 630)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Adam's calendar is wide open (no busy intervals).
# So no constraints need to be added for Adam.

# Jose's busy intervals (in minutes since midnight):
# 10:00 to 11:00  -> [600, 660)
# 12:00 to 14:00  -> [720, 840)
# 15:00 to 16:00  -> [900, 960)
jose_busy = [
    (600, 660),
    (720, 840),
    (900, 960)
]
add_busy_constraints(solver, jose_busy)

# Search for the earliest valid meeting time.
found = False
# Since the meeting must finish by 630, the latest start is 630 - 60 = 570.
for t in range(540, 571):
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