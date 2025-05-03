from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
# The meeting must start and finish within work hours.
solver.add(start >= 540, start + duration <= 1020)
# Megan cannot meet before 11:00 (660 minutes)
solver.add(start >= 660)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting [start, start+duration)
# must not overlap with it.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Peter is free all day, so no constraints.

# Patricia's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
patricia_busy = [(660, 690), (750, 780), (810, 840), (960, 990)]
add_busy_constraints(solver, patricia_busy)

# Megan's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 16:30 -> [900, 990)
megan_busy = [(540, 630), (660, 720), (750, 870), (900, 990)]
add_busy_constraints(solver, megan_busy)

# Amber's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 13:00 -> [660, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
amber_busy = [(570, 630), (660, 780), (810, 840), (870, 900)]
add_busy_constraints(solver, amber_busy)

# Try to find a valid meeting time by iterating over possible start times.
solution_found = False
for t in range(660, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        start_hours, start_minutes = divmod(meeting_start, 60)
        end_hours, end_minutes = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hours, start_minutes, end_hours, end_minutes))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")