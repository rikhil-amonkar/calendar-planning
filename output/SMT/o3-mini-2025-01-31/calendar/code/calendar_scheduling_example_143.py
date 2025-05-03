from z3 import *

solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
# Peter prefers not to have meetings before 14:30 (870 minutes)
solver.add(start >= 870, start + duration <= 1020)

# Helper function: for each busy interval [bs, be),
# ensure that the meeting [start, start+duration) does not overlap.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Marilyn's busy interval:
# 9:00 to 10:00 -> [540, 600]
marilyn_busy = [(540, 600)]
add_busy_constraints(solver, marilyn_busy)

# Timothy's busy intervals:
# 9:00 to 9:30 -> [540, 570]
# 10:00 to 10:30 -> [600, 630]
timothy_busy = [(540, 570), (600, 630)]
add_busy_constraints(solver, timothy_busy)

# Peter's busy intervals:
# 9:30 to 12:30 -> [570, 750]
# 13:00 to 14:30 -> [780, 870]
# 15:00 to 15:30 -> [900, 930]
# 16:00 to 17:00 -> [960, 1020]
peter_busy = [(570, 750), (780, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, peter_busy)

# Patrick's busy intervals:
# 9:00 to 10:00  -> [540, 600]
# 11:00 to 12:30 -> [660, 750]
# 13:00 to 13:30 -> [780, 810]
# 14:00 to 15:00 -> [840, 900]
patrick_busy = [(540, 600), (660, 750), (780, 810), (840, 900)]
add_busy_constraints(solver, patrick_busy)

# Find a valid meeting start time by scanning possible times.
solution_found = False
# The meeting can start at any time t from 870 to 1020 - duration = 990
for t in range(870, 1020 - duration + 1):
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