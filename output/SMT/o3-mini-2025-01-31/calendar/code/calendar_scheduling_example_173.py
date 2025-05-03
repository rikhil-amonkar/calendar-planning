from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')

# General work hours constraint.
solver.add(start >= 540, start + duration <= 1020)

# Harold's preference: do not meet on Monday after 13:00.
# This means the meeting must finish by 13:00 (780 minutes), so:
solver.add(start + duration <= 780)

# Helper function to add busy constraints.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must not overlap with busy interval [bs, be).
        solver.add(Or(start + duration <= bs, start >= be))

# Jacqueline's busy intervals.
# 9:00 to 9:30  -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:00 -> [930, 960)
jacqueline_busy = [(540, 570), (660, 690), (750, 780), (930, 960)]
add_busy_constraints(solver, jacqueline_busy)

# Harold's busy intervals.
# 10:00 to 10:30 -> [600, 630)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 17:00 -> [900, 1020)
harold_busy = [(600, 630), (780, 810), (900, 1020)]
add_busy_constraints(solver, harold_busy)

# Arthur's busy intervals.
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:30 -> [600, 750)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 17:00 -> [930, 1020)
arthur_busy = [(540, 570), (600, 750), (870, 900), (930, 1020)]
add_busy_constraints(solver, arthur_busy)

# Kelly's busy intervals.
# 9:00 to 9:30  -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:00 -> [930, 960)
kelly_busy = [(540, 570), (600, 660), (690, 750), (840, 900), (930, 960)]
add_busy_constraints(solver, kelly_busy)

# Find the earliest valid meeting start time that satisfies all constraints.
solution_found = False
# Because of Harold's preference (meeting must finish by 13:00),
# the latest valid start time is 750 (since 750 + 30 = 780).
for t in range(540, 751):
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