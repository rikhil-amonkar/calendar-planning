from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
# General working hours constraint
solver.add(start >= 540, start + duration <= 1020)
# Gary's preference: would rather not meet after 10:00
solver.add(start + duration <= 600)  # Meeting must end by 10:00

# Helper function: For each busy interval [bs, be), ensure the meeting interval [start, start+duration)
# does not overlap with the busy period.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Gary's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:00 to 12:30 -> [720, 750)
gary_busy = [(570, 600), (720, 750)]
add_busy_constraints(solver, gary_busy)

# Douglas's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
douglas_busy = [(630, 660), (690, 720), (840, 870), (990, 1020)]
add_busy_constraints(solver, douglas_busy)

# Elizabeth's busy intervals:
# 11:30 to 13:30 -> [690, 810)
# 14:00 to 15:00 -> [840, 900)
# 16:00 to 17:00 -> [960, 1020)
elizabeth_busy = [(690, 810), (840, 900), (960, 1020)]
add_busy_constraints(solver, elizabeth_busy)

# Daniel's busy intervals:
# 10:30 to 12:30 -> [630, 750)
# 14:00 to 17:00 -> [840, 1020)
daniel_busy = [(630, 750), (840, 1020)]
add_busy_constraints(solver, daniel_busy)

# Search for the earliest valid meeting start time.
solution_found = False
# Because of Gary's constraint (meeting must end by 10:00), the latest meeting start is 9:30 (570 minutes).
for t in range(540, 571):  # 540 to 570 inclusive.
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
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