from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Given a list of busy intervals (busy_start, busy_end),
# add constraints so that the meeting [start, start+duration) does not overlap with any interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Mason's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 16:00 to 16:30 -> [960, 990)
mason_busy = [(660, 690), (960, 990)]
add_busy_constraints(solver, mason_busy)

# Anthony's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
anthony_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, anthony_busy)

# Teresa's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:00 -> [780, 840)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
teresa_busy = [(570, 600), (660, 690), (780, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, teresa_busy)

# Katherine's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 15:00 -> [780, 900)
# 16:00 to 17:00 -> [960, 1020)
katherine_busy = [(540, 630), (660, 750), (780, 900), (960, 1020)]
add_busy_constraints(solver, katherine_busy)

# Brian's busy intervals:
# 9:30 to 12:00  -> [570, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
brian_busy = [(570, 720), (750, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, brian_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Latest valid start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert meeting start and end from minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")