from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval, ensure that the meeting does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Margaret's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
margaret_busy = [(570, 630), (720, 750), (840, 870)]
add_busy_constraints(solver, margaret_busy)

# Justin's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 13:30 to 14:00 -> [810, 840)
justin_busy = [(570, 600), (810, 840)]
add_busy_constraints(solver, justin_busy)

# Noah's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
noah_busy = [(600, 630), (690, 720), (750, 780), (840, 870)]
add_busy_constraints(solver, noah_busy)

# Madison's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
madison_busy = [(570, 630), (660, 690), (780, 810), (840, 900)]
add_busy_constraints(solver, madison_busy)

# Carl's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 12:00   -> [660, 720)
# 12:30 to 13:30   -> [750, 810)
# 14:00 to 14:30   -> [840, 870)
# 15:00 to 15:30   -> [900, 930)
# 16:00 to 16:30   -> [960, 990)
carl_busy = [(570, 600), (660, 720), (750, 810), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, carl_busy)

# Denise's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:30 to 14:30 -> [690, 870)
# 15:00 to 16:30 -> [900, 990)
denise_busy = [(540, 630), (690, 870), (900, 990)]
add_busy_constraints(solver, denise_busy)

# Mason's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 14:00  -> [690, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:00 to 16:30  -> [960, 990)
mason_busy = [(570, 600), (630, 660), (690, 840), (870, 930), (960, 990)]
add_busy_constraints(solver, mason_busy)

# Try possible meeting start times within work hours.
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