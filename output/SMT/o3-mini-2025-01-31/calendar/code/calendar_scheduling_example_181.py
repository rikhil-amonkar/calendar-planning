from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Amanda's preference: cannot meet before 16:00.
# 16:00 in minutes = 960, so the meeting must start at or after 960.
solver.add(start >= 960)

# Helper function to add constraints so that the meeting interval [start, start+duration)
# does not overlap with any busy interval [bs, be).
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Samuel is free the entire day, so no busy intervals.

# Evelyn's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#  11:00 to 12:00   -> [660, 720)
#  12:30 to 13:00   -> [750, 780)
#  15:30 to 16:00   -> [930, 960)
evelyn_busy = [(540, 600), (660, 720), (750, 780), (930, 960)]
add_busy_constraints(solver, evelyn_busy)

# Ruth's busy intervals:
#   9:30 to 11:00   -> [570, 660)
#  11:30 to 12:30   -> [690, 750)
#  13:00 to 13:30   -> [780, 810)
#  14:00 to 14:30   -> [840, 870)
#  15:00 to 16:00   -> [900, 960)
#  16:30 to 17:00   -> [990, 1020)
ruth_busy = [(570, 660), (690, 750), (780, 810), (840, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, ruth_busy)

# Amanda's busy intervals:
#  10:00 to 10:30   -> [600, 630)
#  11:00 to 12:30   -> [660, 750)
#  13:00 to 13:30   -> [780, 810)
#  14:00 to 15:00   -> [840, 900)
#  15:30 to 16:00   -> [930, 960)
amanda_busy = [(600, 630), (660, 750), (780, 810), (840, 900), (930, 960)]
add_busy_constraints(solver, amanda_busy)

# Because Amanda cannot meet before 16:00 (960) and meeting must finish by 17:00,
# the meeting start time must be within [960, 990].
solution_found = False
for t in range(960, 991):  # 960 to 990 inclusive possible start times.
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")