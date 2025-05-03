from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start+duration)
# must either finish before the busy interval starts or begin after the busy interval ends.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jacob's busy intervals:
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
jacob_busy = [(840, 870), (900, 930)]
add_busy_constraints(solver, jacob_busy)

# Frances's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
frances_busy = [(810, 840), (960, 990)]
add_busy_constraints(solver, frances_busy)

# Emily's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
emily_busy = [(750, 780), (840, 870)]
add_busy_constraints(solver, emily_busy)

# Mark is free the entire day, so no constraints needed.

# Linda's busy intervals:
# 10:00 to 12:00 -> [600, 720)
# 13:00 to 14:30 -> [780, 870)
# 15:30 to 16:00 -> [930, 960)
linda_busy = [(600, 720), (780, 870), (930, 960)]
add_busy_constraints(solver, linda_busy)

# Robert's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 13:30  -> [660, 810)
# 14:00 to 14:30  -> [840, 870)
# 16:00 to 16:30  -> [960, 990)
robert_busy = [(570, 600), (660, 810), (840, 870), (960, 990)]
add_busy_constraints(solver, robert_busy)

# Raymond's busy intervals:
# 9:30 to 11:30   -> [570, 690)
# 12:30 to 16:00  -> [750, 960)
# 16:30 to 17:00  -> [990, 1020)
raymond_busy = [(570, 690), (750, 960), (990, 1020)]
add_busy_constraints(solver, raymond_busy)

# Try to find a valid meeting start time by iterating over each possible minute.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")