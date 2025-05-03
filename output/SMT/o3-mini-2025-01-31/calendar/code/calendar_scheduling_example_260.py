from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 to 17:00 (in minutes, 9:00 = 540, 17:00 = 1020)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints requiring that the meeting interval [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Sharon is free, so no constraints.

# Ryan's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
ryan_busy = [(600, 660), (750, 780), (840, 870)]
add_busy_constraints(solver, ryan_busy)

# Isabella's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
isabella_busy = [(660, 690), (840, 870)]
add_busy_constraints(solver, isabella_busy)

# Anna's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 11:30  -> [660, 690)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 17:00  -> [900, 1020)
anna_busy = [(540, 600), (660, 690), (780, 870), (900, 1020)]
add_busy_constraints(solver, anna_busy)

# Vincent's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 13:30 to 16:00 -> [810, 960)
vincent_busy = [(540, 570), (600, 630), (690, 720), (810, 960)]
add_busy_constraints(solver, vincent_busy)

# Find the earliest valid meeting start time.
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