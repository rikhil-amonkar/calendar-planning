from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start+duration)
# must either finish before busy_start or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Christopher's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
christopher_busy = [(540, 570), (660, 690), (720, 750), (780, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, christopher_busy)

# Karen's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
karen_busy = [(540, 570), (720, 750), (780, 810), (840, 870)]
add_busy_constraints(solver, karen_busy)

# Patricia's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 15:00 to 15:30 -> [900, 930)
patricia_busy = [(540, 570), (630, 660), (690, 720), (900, 930)]
add_busy_constraints(solver, patricia_busy)

# Charlotte's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
charlotte_busy = [(600, 630), (660, 690), (840, 870), (990, 1020)]
add_busy_constraints(solver, charlotte_busy)

# Roger's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 12:00 to 13:30  -> [720, 810)
# 14:00 to 15:00  -> [840, 900)
# 15:30 to 16:30  -> [930, 990)
roger_busy = [(540, 570), (720, 810), (840, 900), (930, 990)]
add_busy_constraints(solver, roger_busy)

# Anna's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:30  -> [600, 690)
# 12:00 to 17:00  -> [720, 1020)
anna_busy = [(540, 570), (600, 690), (720, 1020)]
add_busy_constraints(solver, anna_busy)

# Dylan's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 15:30 -> [810, 930)
# 16:30 to 17:00 -> [990, 1020)
dylan_busy = [(630, 660), (720, 780), (810, 930), (990, 1020)]
add_busy_constraints(solver, dylan_busy)

# Try to find a valid meeting start time by iterating over each possible minute.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")