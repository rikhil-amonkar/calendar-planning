from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints based on a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be) the meeting must either finish no later than bs or start no earlier than be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Willie’s busy intervals:
# 12:00 to 12:30 -> [720, 750]
# 15:30 to 16:00 -> [930, 960]
willie_busy = [(720, 750), (930, 960)]
add_busy_constraints(solver, willie_busy)

# Charlotte’s busy intervals:
# 9:30 to 10:00  -> [570, 600]
# 14:00 to 14:30 -> [840, 870]
# 15:00 to 16:00 -> [900, 960]
charlotte_busy = [(570, 600), (840, 870), (900, 960)]
add_busy_constraints(solver, charlotte_busy)

# Noah’s busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 12:00 -> [660, 720]
# 13:00 to 15:00 -> [780, 900]
# 15:30 to 17:00 -> [930, 1020]
noah_busy = [(600, 630), (660, 720), (780, 900), (930, 1020)]
add_busy_constraints(solver, noah_busy)

# Evelyn’s busy intervals:
# 9:00 to 10:00   -> [540, 600]
# 10:30 to 11:30  -> [630, 690]
# 13:30 to 16:00  -> [810, 960]
# 16:30 to 17:00  -> [990, 1020]
evelyn_busy = [(540, 600), (630, 690), (810, 960), (990, 1020)]
add_busy_constraints(solver, evelyn_busy)

# Now search for a valid meeting time by iterating over all possible start times.
solution_found = False
# The meeting must finish by 1020 so the start can be in range 540 to 1020-duration = 990.
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