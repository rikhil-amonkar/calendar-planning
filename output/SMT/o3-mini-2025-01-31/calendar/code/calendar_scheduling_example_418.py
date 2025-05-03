from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Ensure the meeting is within work hours:
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before busy interval begins
        # or start after busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jack is free the entire day, so no constraints.

# Dylan's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 16:30 to 17:00 -> [990, 1020)
dylan_busy = [(540, 570), (990, 1020)]
add_busy_constraints(solver, dylan_busy)

# Janice's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
janice_busy = [(570, 600), (720, 750), (840, 870), (990, 1020)]
add_busy_constraints(solver, janice_busy)

# Willie's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 15:00 -> [840, 900)
willie_busy = [(570, 600), (690, 720), (840, 900)]
add_busy_constraints(solver, willie_busy)

# Donna's busy intervals:
# 9:30 to 11:00 -> [570, 660)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 17:00 -> [960, 1020)
donna_busy = [(570, 660), (690, 780), (810, 840), (870, 900), (960, 1020)]
add_busy_constraints(solver, donna_busy)

# Peter's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:30 -> [810, 870)
# 15:30 to 17:00 -> [930, 1020)
peter_busy = [(630, 690), (750, 780), (810, 870), (930, 1020)]
add_busy_constraints(solver, peter_busy)

# Raymond's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 17:00 -> [930, 1020)
raymond_busy = [(540, 570), (630, 660), (750, 810), (870, 900), (930, 1020)]
add_busy_constraints(solver, raymond_busy)

# Now, iterate over possible start times to find one meeting slot that satisfies all constraints.
found = False
# Meeting start must be such that the meeting finishes by 17:00.
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")