from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Betty's preference: avoid meetings after 15:00.
# Therefore, the meeting must finish by 15:00 (900 minutes).
solver.add(start + duration <= 900)

# Helper function:
# Adds constraints to require that the meeting interval [start, start+duration)
# does not overlap with any of the provided busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before a busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Julie's busy intervals:
# 13:30 to 15:30 -> [810, 930)
julie_busy = [(810, 930)]
add_busy_constraints(solver, julie_busy)

# Betty's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
betty_busy = [(630, 660), (780, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, betty_busy)

# Kayla's calendar is wide open, so no busy intervals.

# Heather's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 15:00 -> [810, 900)
heather_busy = [(540, 570), (630, 660), (690, 780), (810, 900)]
add_busy_constraints(solver, heather_busy)

# Keith's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 13:30 -> [690, 810)
# 14:30 to 15:00 -> [870, 900)
keith_busy = [(570, 660), (690, 810), (870, 900)]
add_busy_constraints(solver, keith_busy)

# We want the earliest meeting time that works for everyone.
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