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

# Helper function to add constraints ensuring that the meeting [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before a busy interval begins or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Amber's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:00 to 13:30 -> [780, 810)
# 16:00 to 16:30 -> [960, 990)
amber_busy = [(540, 570), (600, 630), (660, 720), (780, 810), (960, 990)]
add_busy_constraints(solver, amber_busy)

# Christian's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
christian_busy = [(660, 690), (840, 870)]
add_busy_constraints(solver, christian_busy)

# Natalie's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
natalie_busy = [(660, 690), (720, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, natalie_busy)

# Douglas's busy intervals:
# 9:30 to 12:30  -> [570, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
douglas_busy = [(570, 750), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, douglas_busy)

# Larry's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 17:00 -> [840, 1020)
larry_busy = [(540, 570), (600, 630), (720, 780), (840, 1020)]
add_busy_constraints(solver, larry_busy)

# Search for the earliest valid meeting start time.
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