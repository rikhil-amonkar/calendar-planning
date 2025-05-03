from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish before the busy interval starts
        # or begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Dorothy's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 16:00 to 16:30 -> [960, 990)
dorothy_busy = [(600, 630), (690, 720), (750, 780), (960, 990)]
add_busy_constraints(solver, dorothy_busy)

# Kenneth's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
kenneth_busy = [(690, 720), (750, 780)]
add_busy_constraints(solver, kenneth_busy)

# Madison's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 16:30 to 17:00 -> [990, 1020)
madison_busy = [(570, 600), (990, 1020)]
add_busy_constraints(solver, madison_busy)

# Brandon's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 15:30 -> [750, 930)
# 16:00 to 16:30 -> [960, 990)
brandon_busy = [(540, 570), (660, 720), (750, 930), (960, 990)]
add_busy_constraints(solver, brandon_busy)

# Judith's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 16:30 -> [930, 990)
judith_busy = [(600, 630), (660, 690), (720, 750), (810, 900), (930, 990)]
add_busy_constraints(solver, judith_busy)

# Find the earliest meeting time that works for everyone.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")