from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Jose cannot meet after 15:30, so the meeting must finish by 15:30 (930 minutes).
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must start no earlier than 9:00 and finish by 15:30.
solver.add(start >= 540, start + duration <= 930)

# Helper function to add constraints that the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval
        # starts or begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Mason is free the entire day; no busy intervals.

# Evelyn is free the entire day; no busy intervals.

# Jose's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
jose_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, jose_busy)

# Helen's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 14:30 -> [780, 870)
# 15:30 to 16:00 -> [930, 960) -- irrelevant here because meeting must finish by 15:30.
# 16:30 to 17:00 -> [990, 1020) -- irrelevant due to time constraint.
helen_busy = [(540, 570), (660, 720), (780, 870)]
add_busy_constraints(solver, helen_busy)

# Beverly's busy intervals:
# 9:00 to 12:30 -> [540, 750)
# 13:00 to 15:00 -> [780, 900)
# 16:30 to 17:00 -> [990, 1020) -- irrelevant due to time constraint.
beverly_busy = [(540, 750), (780, 900)]
add_busy_constraints(solver, beverly_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Latest start is 930 - duration = 900.
for t in range(540, 901):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")