from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before the busy interval starts
        # or begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Bryan and Lori are free the entire day, so no busy obstacles for them.

# Kimberly's busy intervals:
# 9:30 to 11:00 -> [570, 660)
# 12:00 to 12:30 -> [720, 750)
kimberly_busy = [(570, 660), (720, 750)]
add_busy_constraints(solver, kimberly_busy)

# Beverly's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:30 -> [930, 990)
beverly_busy = [(540, 570), (660, 690), (750, 810), (840, 900), (930, 990)]
add_busy_constraints(solver, beverly_busy)

# Dennis's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 12:00 to 17:00  -> [720, 1020)
dennis_busy = [(570, 690), (720, 1020)]
add_busy_constraints(solver, dennis_busy)

# Look for the earliest valid meeting time.
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