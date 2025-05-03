from z3 import Solver, Int, Or

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints so that the meeting does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must either finish before a busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Douglas's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
douglas_busy = [(690, 720), (810, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, douglas_busy)

# Susan is free the whole day, no busy intervals.
# Donna is free the whole day, no busy intervals.

# Elizabeth's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
elizabeth_busy = [(540, 570), (750, 780), (810, 840), (900, 930)]
add_busy_constraints(solver, elizabeth_busy)

# Ralph's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:30 -> [930, 990)
ralph_busy = [(540, 570), (600, 660), (690, 720), (780, 810), (870, 900), (930, 990)]
add_busy_constraints(solver, ralph_busy)

# Paul's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 16:30  -> [960, 990)
paul_busy = [(540, 600), (690, 750), (780, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, paul_busy)

# Ryan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
ryan_busy = [(540, 570), (600, 630), (750, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, ryan_busy)

# Search for a valid meeting start time.
found = False
# Candidate start times range from 540 to (1020 - duration) inclusive.
for t in range(540, 1020 - duration + 1):
    solver.push()             # Save the current solver state.
    solver.add(start == t)    # Try setting the meeting to a candidate start time.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()   # Restore the solver state.
        break
    solver.pop()       # Restore state if candidate fails.

if not found:
    print("No valid meeting time could be found.")