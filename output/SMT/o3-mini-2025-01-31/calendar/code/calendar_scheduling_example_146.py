from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Define a helper function to add constraints for busy intervals.
# For each busy interval [bs, be), we require that the meeting [start, start+duration)
# does not overlap with the busy interval; i.e., either it ends on or before bs, or it starts on or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Anna's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 11:00 -> [630, 660]
# 12:00 to 12:30 -> [720, 750]
# 14:30 to 15:00 -> [870, 900]
# 16:00 to 17:00 -> [960,1020]
anna_busy = [(540, 570), (630, 660), (720, 750), (870, 900), (960, 1020)]
add_busy_constraints(solver, anna_busy)

# Dennis's busy intervals:
# 12:00 to 13:30 -> [720, 810]
# 15:00 to 15:30 -> [900, 930]
dennis_busy = [(720, 810), (900, 930)]
add_busy_constraints(solver, dennis_busy)

# Zachary's busy intervals:
# 9:00 to 10:30  -> [540, 630]
# 12:00 to 12:30 -> [720, 750]
# 13:00 to 17:00 -> [780, 1020]
zachary_busy = [(540, 630), (720, 750), (780, 1020)]
add_busy_constraints(solver, zachary_busy)

# Bobby's busy intervals:
# 9:30 to 11:00  -> [570, 660]
# 11:30 to 12:00 -> [690, 720]
# 12:30 to 14:30 -> [750, 870]
# 15:00 to 17:00 -> [900, 1020]
bobby_busy = [(570, 660), (690, 720), (750, 870), (900, 1020)]
add_busy_constraints(solver, bobby_busy)

# Try each possible meeting start time within the allowed work hours.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")