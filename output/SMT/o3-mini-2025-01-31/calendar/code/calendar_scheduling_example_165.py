from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), ensure the meeting [start, start+duration)
# does not overlap with the busy period.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Anthony has no meetings, so no busy intervals.

# Stephanie's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:30 to 13:30 -> [750, 810)
# 15:30 to 17:00 -> [930, 1020)
stephanie_busy = [(570, 600), (750, 810), (930, 1020)]
add_busy_constraints(solver, stephanie_busy)

# Emma's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 16:00 -> [840, 960)
emma_busy = [(540, 630), (690, 750), (780, 810), (840, 960)]
add_busy_constraints(solver, emma_busy)

# Kathleen's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 17:00 -> [930, 1020)
kathleen_busy = [(600, 660), (690, 750), (840, 870), (930, 1020)]
add_busy_constraints(solver, kathleen_busy)

# We want the group's meeting to be at their earliest availability.
solution_found = False

# Search for the earliest valid meeting start time.
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")