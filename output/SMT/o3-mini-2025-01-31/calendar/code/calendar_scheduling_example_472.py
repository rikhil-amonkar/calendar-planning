from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) should either end before the busy interval starts,
        # or start after it ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Roy's busy intervals:
# 16:00 to 17:00 -> [960, 1020)
roy_busy = [(960, 1020)]
add_busy_constraints(solver, roy_busy)

# Thomas's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
thomas_busy = [(690, 720), (870, 900)]
add_busy_constraints(solver, thomas_busy)

# John's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
john_busy = [(630, 660), (720, 750), (810, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, john_busy)

# Amy's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
amy_busy = [(540, 570), (810, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, amy_busy)

# Mason's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
mason_busy = [(570, 600), (630, 660), (690, 750), (780, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, mason_busy)

# Zachary's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 14:00 -> [750, 840)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
zachary_busy = [(600, 630), (690, 720), (750, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, zachary_busy)

# Jacqueline's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 16:30 -> [810, 990)
jacqueline_busy = [(570, 600), (630, 660), (690, 750), (810, 990)]
add_busy_constraints(solver, jacqueline_busy)

# Search for the earliest available meeting time.
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