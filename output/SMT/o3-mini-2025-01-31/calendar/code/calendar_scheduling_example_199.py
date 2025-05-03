from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Carol doesn't want to meet before 12:30, i.e., meeting should start at or after 12:30 (750 minutes)
solver.add(start >= 750)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end), ensure the meeting interval [start, start+duration)
    # either ends before busy_start or starts after or at busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Elizabeth's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
elizabeth_busy = [(690, 720), (810, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, elizabeth_busy)

# Christian's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:30 -> [750, 810)
# 15:30 to 17:00 -> [930, 1020)
christian_busy = [(540, 570), (600, 630), (660, 690), (750, 810), (930, 1020)]
add_busy_constraints(solver, christian_busy)

# Isabella's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 12:30 to 13:30 -> [750, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
isabella_busy = [(570, 690), (750, 810), (900, 930), (960, 990)]
add_busy_constraints(solver, isabella_busy)

# Carol is free all day, so no busy intervals for her.

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(750, 991):  # starting at 750 due to Carol's constraint.
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