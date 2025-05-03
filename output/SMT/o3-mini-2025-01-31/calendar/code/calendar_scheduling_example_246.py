from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes since midnight

# Ensure the meeting occurs within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper: add constraints to ensure the meeting does not overlap each busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting must be completely before or completely after a busy interval.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jacob's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
jacob_busy = [(810, 840), (870, 900)]
add_busy_constraints(solver, jacob_busy)

# Diana's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 16:00 to 16:30 -> [960, 990)
diana_busy = [(570, 600), (690, 720), (780, 810), (960, 990)]
add_busy_constraints(solver, diana_busy)

# Adam's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 12:30 -> [660, 750)
# 15:30 to 16:00 -> [930, 960)
adam_busy = [(570, 630), (660, 750), (930, 960)]
add_busy_constraints(solver, adam_busy)

# Angela's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 12:00 -> [630, 720)
# 13:00 to 15:30 -> [780, 930)
# 16:00 to 16:30 -> [960, 990)
angela_busy = [(570, 600), (630, 720), (780, 930), (960, 990)]
add_busy_constraints(solver, angela_busy)

# Dennis's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 13:00 to 15:00 -> [780, 900)
# 16:30 to 17:00 -> [990, 1020)
dennis_busy = [(540, 570), (630, 690), (780, 900), (990, 1020)]
add_busy_constraints(solver, dennis_busy)

# Find the earliest meeting time that satisfies all participant constraints.
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