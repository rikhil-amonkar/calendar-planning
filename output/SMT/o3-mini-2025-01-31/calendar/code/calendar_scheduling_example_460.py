from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must finish before the busy interval
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Katherine's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 15:00 -> [870, 900)
katherine_busy = [(720, 750), (780, 840), (870, 900)]
add_busy_constraints(solver, katherine_busy)

# Douglas's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 13:00 to 13:30 -> [780, 810)
douglas_busy = [(540, 570), (780, 810)]
add_busy_constraints(solver, douglas_busy)

# Ann's busy intervals:
# 14:30 to 15:30 -> [870, 930)
ann_busy = [(870, 930)]
add_busy_constraints(solver, ann_busy)

# Pamela's busy intervals:
# 10:00 to 11:00 -> [600, 660)
pamela_busy = [(600, 660)]
add_busy_constraints(solver, pamela_busy)

# Gloria's busy intervals:
# 9:00 to 12:30 -> [540, 750)
# 13:00 to 15:30 -> [780, 930)
# 16:00 to 17:00 -> [960, 1020)
gloria_busy = [(540, 750), (780, 930), (960, 1020)]
add_busy_constraints(solver, gloria_busy)

# Donna's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 15:00 -> [810, 900)
# 16:00 to 17:00 -> [960, 1020)
donna_busy = [(540, 570), (630, 660), (750, 780), (810, 900), (960, 1020)]
add_busy_constraints(solver, donna_busy)

# Christopher's busy intervals:
# 9:30 to 11:00 -> [570, 660)
# 11:30 to 15:30 -> [690, 930)
# 16:30 to 17:00 -> [990, 1020)
christopher_busy = [(570, 660), (690, 930), (990, 1020)]
add_busy_constraints(solver, christopher_busy)

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