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

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before the busy interval starts or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Doris's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 16:30 to 17:00 -> [990, 1020)
doris_busy = [(630, 660), (990, 1020)]
add_busy_constraints(solver, doris_busy)

# Dennis's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:00  -> [930, 960)
dennis_busy = [(570, 600), (630, 660), (840, 870), (930, 960)]
add_busy_constraints(solver, dennis_busy)

# Matthew's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 13:00 to 13:30  -> [780, 810)
# 15:00 to 15:30  -> [900, 930)
matthew_busy = [(570, 630), (780, 810), (900, 930)]
add_busy_constraints(solver, matthew_busy)

# Andrea's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 10:30 to 11:30   -> [630, 690)
# 12:00 to 13:00   -> [720, 780)
# 14:00 to 14:30   -> [840, 870)
# 15:30 to 17:00   -> [930, 1020)
andrea_busy = [(540, 600), (630, 690), (720, 780), (840, 870), (930, 1020)]
add_busy_constraints(solver, andrea_busy)

# Brandon's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 17:00  -> [780, 1020)
brandon_busy = [(540, 690), (720, 750), (780, 1020)]
add_busy_constraints(solver, brandon_busy)

# Find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
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