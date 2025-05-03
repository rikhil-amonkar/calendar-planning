from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # duration in minutes
start = Int("start")  # meeting start time in minutes from midnight

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Sara would like to avoid meetings after 11:00.
# This means the meeting must finish by 11:00 (660 minutes).
solver.add(start + duration <= 660)

# Helper function to add constraints so that the meeting does not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Sara's busy intervals (in minutes since midnight):
# 10:00 to 10:30 -> [600, 630)
# 13:00 to 14:00 -> [780, 840)
# 16:30 to 17:00 -> [990, 1020)
sara_busy = [
    (600, 630),
    (780, 840),
    (990, 1020)
]
add_busy_constraints(solver, sara_busy)

# Randy's busy intervals (in minutes since midnight):
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 17:00 -> [840, 1020)
randy_busy = [
    (540, 570),
    (630, 690),
    (750, 780),
    (840, 1020)
]
add_busy_constraints(solver, randy_busy)

# Search for the earliest valid meeting time.
found = False
# Due to the constraint that the meeting must finish by 11:00,
# the latest start time is 660 - duration = 630.
for t in range(540, 631):
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