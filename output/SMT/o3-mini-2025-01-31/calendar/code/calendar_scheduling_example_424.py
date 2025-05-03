from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Add constraints so that the meeting does not clash with given busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting should either finish before the busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Julie is free the entire day; no constraints needed.

# Marilyn's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 15:00 to 15:30 -> [900, 930)
marilyn_busy = [(570, 600), (900, 930)]
add_busy_constraints(solver, marilyn_busy)

# Olivia is free the entire day; no constraints.

# Emily's busy interval:
# 12:30 to 13:30 -> [750, 810)
emily_busy = [(750, 810)]
add_busy_constraints(solver, emily_busy)

# Bruce's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 16:00  -> [840, 960)
# 16:30 to 17:00  -> [990, 1020)
bruce_busy = [(540, 720), (750, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, bruce_busy)

# Jeffrey's busy intervals:
# 9:00 to 14:30   -> [540, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
jeffrey_busy = [(540, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, jeffrey_busy)

# Kyle's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 11:00 to 12:30   -> [660, 750)
# 13:30 to 15:00   -> [810, 900)
# 15:30 to 16:00   -> [930, 960)
# 16:30 to 17:00   -> [990, 1020)
kyle_busy = [(540, 600), (660, 750), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, kyle_busy)

# Search for a valid meeting time slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_minute = divmod(meeting_start, 60)
        end_hour, end_minute = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hour, start_minute, end_hour, end_minute))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")