from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Raymond prefers not to have meetings after 11:30.
# Therefore, we require that the meeting ends by 11:30 (690 minutes).
solver.add(start + duration <= 690)

# Helper function to add non-overlap constraints.
# For each busy interval [busy_start, busy_end), the meeting interval
# [start, start+duration) must either finish by busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Cheryl's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 16:30 -> [900, 990)
cheryl_busy = [(690, 720), (780, 840), (900, 990)]
add_busy_constraints(solver, cheryl_busy)

# Raymond's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:30 -> [870, 930)
raymond_busy = [(660, 690), (780, 810), (870, 930)]
add_busy_constraints(solver, raymond_busy)

# Karen's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 14:00  -> [780, 840)
# 16:30 to 17:00  -> [990, 1020)
karen_busy = [(540, 630), (660, 690), (720, 750), (780, 840), (990, 1020)]
add_busy_constraints(solver, karen_busy)

# Joan's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 12:30  -> [660, 750)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:30 to 17:00  -> [990, 1020)
joan_busy = [(540, 630), (660, 750), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, joan_busy)

# Since Raymond's preference confines the meeting to the morning (meeting end <= 690),
# the possible start times are from 540 (9:00) up to 660 (so that meeting ends by 690).
solution_found = False
for t in range(540, 661):  # t in [540, 660]
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")