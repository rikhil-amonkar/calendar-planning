from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Given busy intervals (start, end) in minutes,
# the meeting must not overlap with any interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting [start, start+duration) must finish before busy_start or start at/after busy_end.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Natalie busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
natalie_busy = [(600, 630), (660, 690)]
add_busy_constraints(solver, natalie_busy)

# Dylan busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 13:00 to 13:30 -> [780, 810)
dylan_busy = [(540, 570), (780, 810)]
add_busy_constraints(solver, dylan_busy)

# Pamela busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
pamela_busy = [(690, 720), (810, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, pamela_busy)

# Charlotte is free all day, no busy intervals.

# Ann busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 17:00 -> [870, 1020)
ann_busy = [(600, 660), (690, 750), (780, 810), (870, 1020)]
add_busy_constraints(solver, ann_busy)

# Jason busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 13:30 -> [600, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 17:00 -> [930, 1020)
jason_busy = [(540, 570), (600, 810), (840, 870), (930, 1020)]
add_busy_constraints(solver, jason_busy)

# Benjamin busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 16:00 -> [900, 960)
benjamin_busy = [(600, 660), (750, 870), (900, 960)]
add_busy_constraints(solver, benjamin_busy)

# Iterate over possible meeting start times (each minute) within work hours.
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