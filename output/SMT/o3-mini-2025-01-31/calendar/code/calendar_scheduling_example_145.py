from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), ensure the meeting [start, start+duration)
    # does not overlap with the busy time.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Marilyn has no meetings all day.
# Carolyn's busy intervals:
# 10:30 to 11:00 -> [630,660)
# 12:00 to 12:30 -> [720,750)
# 13:00 to 13:30 -> [780,810)
# 16:00 to 16:30 -> [960,990)
carolyn_busy = [(630, 660), (720, 750), (780, 810), (960, 990)]
add_busy_constraints(solver, carolyn_busy)

# Charles's busy intervals:
# 10:30 to 12:00 -> [630,720)
# 13:00 to 14:30 -> [780,870)
# 15:30 to 16:30 -> [930,990)
charles_busy = [(630, 720), (780, 870), (930, 990)]
add_busy_constraints(solver, charles_busy)

# Lori's busy intervals:
# 9:30 to 13:00  -> [570,780)
# 13:30 to 17:00 -> [810,1020)
lori_busy = [(570, 780), (810, 1020)]
add_busy_constraints(solver, lori_busy)

# Try possible meeting start times from 9:00 (540 minutes) 
# to the latest start time (1020 - duration = 990 minutes).
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