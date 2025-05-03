from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 60 minutes.
duration = 60
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function:
# Given a list of busy intervals (busy_start, busy_end) in minutes, ensures that 
# the meeting slot [start, start+duration) does NOT overlap any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Amber's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
amber_busy = [(750, 780), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, amber_busy)

# Alice's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 15:30 to 16:00 -> [930, 960)
alice_busy = [(660, 690), (930, 960)]
add_busy_constraints(solver, alice_busy)

# Brian is free, no busy intervals.

# Ryan's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 17:00 -> [870, 1020)
ryan_busy = [(660, 690), (750, 810), (870, 1020)]
add_busy_constraints(solver, ryan_busy)

# Jonathan's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 17:00 -> [900, 1020)
jonathan_busy = [(630, 660), (690, 720), (750, 870), (900, 1020)]
add_busy_constraints(solver, jonathan_busy)

# Search for the earliest valid meeting time.
solution_found = False
# The latest valid start time is 1020 - 60 = 960.
for t in range(540, 961):
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