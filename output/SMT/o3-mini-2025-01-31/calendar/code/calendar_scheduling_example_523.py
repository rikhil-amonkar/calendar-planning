from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time (in minutes since midnight)

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [b_start, b_end), ensure that the meeting
    # interval [start, start+duration) does not overlap.
    for b_start, b_end in busy_intervals:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Ryan's busy intervals (in minutes):
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
ryan_busy = [
    (540, 570),
    (690, 720),
    (870, 900),
    (960, 990)
]
add_busy_constraints(solver, ryan_busy)

# Kenneth's busy intervals (in minutes):
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:30 -> [870, 990)
kenneth_busy = [
    (570, 630),
    (660, 720),
    (750, 780),
    (810, 840),
    (870, 990)
]
add_busy_constraints(solver, kenneth_busy)

# Search for the earliest valid meeting time.
found = False
# The meeting must finish by 1020, so the latest possible start is 1020 - duration.
for t in range(540, 1020 - duration + 1):
    solver.push()  # save current state
    solver.add(start == t)
    if solver.check() == sat:
        # If a valid assignment is found, extract the meeting time.
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()  # restore state before breaking
        break
    solver.pop()  # restore for next iteration

if not found:
    print("No valid meeting time could be found.")