from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Emma cannot meet before 12:30, which is 750 minutes.
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 750, start + duration <= 1020)

# Helper function: for each busy interval [bs, be),
# the meeting [start, start+duration) must either end on or before bs or begin at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Juan has an open schedule, no busy intervals.
# Emma's busy intervals:
#   9:30 to 10:30 -> [570, 630]
#   12:30 to 13:30 -> [750, 810]
emma_busy = [(570, 630), (750, 810)]
add_busy_constraints(solver, emma_busy)

# Gloria's busy intervals:
#   9:00 to 9:30   -> [540, 570]
#   10:00 to 10:30 -> [600, 630]
#   11:00 to 11:30 -> [660, 690]
#   12:30 to 14:00 -> [750, 840]
#   16:00 to 17:00 -> [960, 1020]
gloria_busy = [(540, 570), (600, 630), (660, 690), (750, 840), (960, 1020)]
add_busy_constraints(solver, gloria_busy)

# Joan's busy intervals:
#   9:00 to 9:30   -> [540, 570]
#   10:00 to 12:00 -> [600, 720]
#   13:00 to 14:00 -> [780, 840]
#   14:30 to 17:00 -> [870, 1020]
joan_busy = [(540, 570), (600, 720), (780, 840), (870, 1020)]
add_busy_constraints(solver, joan_busy)

# Look for a valid meeting time by scanning possible start times.
solution_found = False
# Since meeting duration is 30 minutes, possible start times range from 750 to 990 (inclusive).
for t in range(750, 1020 - duration + 1):
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