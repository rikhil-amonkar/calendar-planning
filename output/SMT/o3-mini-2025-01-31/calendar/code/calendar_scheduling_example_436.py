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

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either finish before busy_start or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Patrick's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
patrick_busy = [(810, 840), (870, 900)]
add_busy_constraints(solver, patrick_busy)

# Shirley's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 17:00  -> [960, 1020)
shirley_busy = [(540, 570), (660, 690), (720, 750), (870, 900), (960, 1020)]
add_busy_constraints(solver, shirley_busy)

# Jeffrey's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 13:30  -> [780, 810)
# 16:00 to 17:00  -> [960, 1020)
jeffrey_busy = [(540, 570), (630, 660), (690, 720), (780, 810), (960, 1020)]
add_busy_constraints(solver, jeffrey_busy)

# Gloria's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 15:00 to 15:30  -> [900, 930)
gloria_busy = [(690, 720), (900, 930)]
add_busy_constraints(solver, gloria_busy)

# Nathan's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 12:00  -> [630, 720)
# 14:00 to 17:00  -> [840, 1020)
nathan_busy = [(540, 570), (630, 720), (840, 1020)]
add_busy_constraints(solver, nathan_busy)

# Angela's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 12:30 to 15:00  -> [750, 900)
# 15:30 to 16:30  -> [930, 990)
angela_busy = [(540, 570), (600, 660), (750, 900), (930, 990)]
add_busy_constraints(solver, angela_busy)

# David's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 10:30  -> [600, 630)
# 11:00 to 14:00  -> [660, 840)
# 14:30 to 16:30  -> [870, 990)
david_busy = [(540, 570), (600, 630), (660, 840), (870, 990)]
add_busy_constraints(solver, david_busy)

# Search for a valid meeting start time by iterating over each possible minute.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}.".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")