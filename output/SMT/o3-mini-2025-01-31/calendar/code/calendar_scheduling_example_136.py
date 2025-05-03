from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Diana cannot meet before 9:30, so start must be at least 570 minutes.
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 570, start + duration <= 1020)

# Helper function to add constraints that prevent overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must end on or before bs, or start on or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Diana's busy intervals:
# 10:30 to 11:00 -> [630, 660]
# 11:30 to 12:00 -> [690, 720]
# 13:30 to 14:00 -> [810, 840]
# 14:30 to 15:00 -> [870, 900]
# 16:00 to 17:00 -> [960, 1020]
diana_busy = [(630, 660), (690, 720), (810, 840), (870, 900), (960, 1020)]
add_busy_constraints(solver, diana_busy)

# Gerald's busy intervals:
# 9:30 to 10:00 -> [570, 600]
# 12:30 to 13:00 -> [750, 780]
# 15:00 to 15:30 -> [900, 930]
# 16:00 to 16:30 -> [960, 990]
gerald_busy = [(570, 600), (750, 780), (900, 930), (960, 990)]
add_busy_constraints(solver, gerald_busy)

# Timothy's busy intervals:
# 10:00 to 12:00 -> [600, 720]
# 12:30 to 14:00 -> [750, 840]
# 14:30 to 15:00 -> [870, 900]
# 16:00 to 17:00 -> [960, 1020]
timothy_busy = [(600, 720), (750, 840), (870, 900), (960, 1020)]
add_busy_constraints(solver, timothy_busy)

# Julie's busy intervals:
# 9:30 to 10:00 -> [570, 600]
# 10:30 to 11:00 -> [630, 660]
# 11:30 to 15:30 -> [690, 930]
# 16:00 to 17:00 -> [960, 1020]
julie_busy = [(570, 600), (630, 660), (690, 930), (960, 1020)]
add_busy_constraints(solver, julie_busy)

# Check for a valid meeting time by searching possible start times.
solution_found = False
for t in range(570, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")