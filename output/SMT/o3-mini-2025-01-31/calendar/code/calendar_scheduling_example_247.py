from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure the meeting [start, start+duration) does not overlap any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting must finish before the busy period starts, or start after the busy period ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Charles' busy intervals:
# 11:00 to 12:30 -> [660, 750)
# 16:30 to 17:00 -> [990, 1020)
charles_busy = [(660, 750), (990, 1020)]
add_busy_constraints(solver, charles_busy)

# Bryan's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 17:00 -> [930, 1020)
bryan_busy = [(810, 840), (930, 1020)]
add_busy_constraints(solver, bryan_busy)

# Ruth is free the entire day, so no busy intervals.

# Keith's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 17:00 -> [870, 1020)
keith_busy = [(540, 570), (600, 630), (690, 720), (780, 840), (870, 1020)]
add_busy_constraints(solver, keith_busy)

# William's busy intervals:
# 9:00 to 11:30  -> [540, 690)
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:30 -> [930, 990)
william_busy = [(540, 690), (750, 780), (930, 990)]
add_busy_constraints(solver, william_busy)

# Find the earliest meeting time that works for everyone.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")