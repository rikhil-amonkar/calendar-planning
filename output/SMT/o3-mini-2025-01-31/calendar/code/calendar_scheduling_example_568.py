from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: between 9:00 (540) and 17:00 (1020)
solver.add(start >= 540, start + duration <= 1020)

# Julia prefers not to have meetings on Monday after 12:30.
# We ensure that the meeting finishes by 12:30 (750 minutes).
solver.add(start + duration <= 750)

# Helper function to constrain meeting to not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Julia's busy intervals (in minutes since midnight):
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
# Even though these intervals are later in the day, Julia's preference already rules out meetings after 12:30.
julia_busy = [
    (900, 930),
    (960, 990)
]
add_busy_constraints(solver, julia_busy)

# Pamela's busy intervals (in minutes since midnight):
# 11:00 to 13:30 -> [660, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 16:30 -> [960, 990)
pamela_busy = [
    (660, 810),
    (870, 930),
    (960, 990)
]
add_busy_constraints(solver, pamela_busy)

# Search for the earliest valid meeting time.
found = False

# The meeting must finish by 12:30 (750), so the latest possible start is 750 - 30 = 720 minutes.
for t in range(540, 721):
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