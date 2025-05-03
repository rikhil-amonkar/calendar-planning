from z3 import *

# Create a solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval [bs, be),
# the meeting [start, start+duration) must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for (bs, be) in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Diane is free all day -> no busy intervals.

# Olivia's busy intervals:
# 10:30 to 11:00 -> [630, 660]
# 16:00 to 16:30 -> [960, 990]
olivia_busy = [(630, 660), (960, 990)]
add_busy_constraints(solver, olivia_busy)

# Vincent's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 12:00 -> [630, 720]
# 12:30 to 15:00 -> [750, 900]
# 15:30 to 17:00 -> [930,1020]
vincent_busy = [(540, 570), (630, 720), (750, 900), (930, 1020)]
add_busy_constraints(solver, vincent_busy)

# Steven's busy intervals:
# 9:00 to 10:30  -> [540, 630]
# 11:00 to 12:00 -> [660, 720]
# 12:30 to 17:00 -> [750,1020]
steven_busy = [(540, 630), (660, 720), (750, 1020)]
add_busy_constraints(solver, steven_busy)

# Try possible meeting start times from 9:00 (540) up to (1020 - duration) = 990.
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