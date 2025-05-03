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

# Aaron's preference: He would like to avoid more meetings on Monday after 10:30.
# We interpret this as the meeting needing to end by 10:30 (i.e., by 630 minutes).
solver.add(start + duration <= 630)

# Helper function to add non-overlap constraints for each busy interval.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must either finish 
    # at or before busy_start, or start at or after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Aaron is free all day, so no busy intervals for him.

# Donna's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
donna_busy = [(690, 720), (870, 900)]
add_busy_constraints(solver, donna_busy)

# Andrea's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 14:00 -> [690, 840)
# 15:30 to 16:30 -> [930, 990)
andrea_busy = [(540, 570), (690, 840), (930, 990)]
add_busy_constraints(solver, andrea_busy)

# Dylan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 17:00 -> [690, 1020)
dylan_busy = [(540, 570), (600, 660), (690, 1020)]
add_busy_constraints(solver, dylan_busy)

# Search for a valid start time.
solution_found = False
# Due to Aaron's constraint (meeting must end by 10:30), the latest possible start is 630 - 30 = 600.
for t in range(540, 601):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")