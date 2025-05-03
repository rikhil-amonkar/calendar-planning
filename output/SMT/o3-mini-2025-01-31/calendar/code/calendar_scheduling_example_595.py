from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Christina's busy intervals (in minutes since midnight):
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
christina_busy = [
    (600, 630),
    (660, 690),
    (720, 750),
    (780, 810),
    (870, 900),
    (930, 960)
]
add_busy_constraints(solver, christina_busy)

# Elizabeth's busy intervals (in minutes since midnight):
# 9:00 to 12:30  -> [540, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:30 -> [840, 930)
# 16:30 to 17:00 -> [990, 1020)
elizabeth_busy = [
    (540, 750),
    (780, 810),
    (840, 930),
    (990, 1020)
]
add_busy_constraints(solver, elizabeth_busy)

# Since we would like to schedule the meeting at the earliest availability,
# we search for the earliest valid meeting time.
found = False
# The latest valid start is 1020 - duration = 990.
for t in range(540, 991):
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