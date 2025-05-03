from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration is half an hour
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: Meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Roy does not want to meet on Monday after 12:00.
# Therefore, the meeting must finish by 12:00, i.e., start + duration <= 720.
solver.add(start + duration <= 720)

# Helper function to add busy interval constraints to the solver.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure that the meeting interval [start, start+duration) does not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Dennis's busy intervals (in minutes since midnight):
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:30 -> [870, 930)
dennis_busy = [
    (630, 660),
    (720, 750),
    (870, 930)
]
add_busy_constraints(solver, dennis_busy)

# Roy's busy intervals (in minutes since midnight):
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 15:00 -> [780, 900)
# 15:30 to 17:00 -> [930, 1020)
roy_busy = [
    (540, 570),
    (600, 660),
    (690, 750),
    (780, 900),
    (930, 1020)
]
add_busy_constraints(solver, roy_busy)

# Search for the earliest valid meeting time.
found = False
# Since the meeting must finish by 720, the latest start is 720 - 30 = 690.
for t in range(540, 691):
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