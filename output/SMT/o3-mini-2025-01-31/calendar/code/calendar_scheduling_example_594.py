from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Define work hours: meeting must be scheduled between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Ensure the meeting interval [start, start+duration) does NOT overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Adam's busy intervals (in minutes since midnight):
# 9:30 to 10:00 -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
adam_busy = [
    (570, 600),
    (750, 780),
    (870, 900),
    (990, 1020)
]
add_busy_constraints(solver, adam_busy)

# Roy's busy intervals (in minutes since midnight):
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 14:30 -> [810, 870)
# 16:30 to 17:00 -> [990, 1020)
roy_busy = [
    (600, 660),
    (690, 780),
    (810, 870),
    (990, 1020)
]
add_busy_constraints(solver, roy_busy)

# Since the group would like to meet at their earliest availability,
# we search for the earliest valid start time.
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