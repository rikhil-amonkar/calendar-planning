from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int('start')

# Megan's preference: no meetings before 10:00.
# So the meeting must start at or after 10:00 (600 minutes)
solver.add(start >= 600)
# Also, meeting must finish by 17:00.
solver.add(start + duration <= 1020)

# Helper function: add constraints to avoid overlapping busy intervals.
# For a busy interval [busy_start, busy_end), the meeting (from start to start+duration)
# must either finish by busy_start or start after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Kimberly's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 12:00 -> [660, 720)
#   16:00 to 16:30 -> [960, 990)
kimberly_busy = [(600, 630), (660, 720), (960, 990)]
add_busy_constraints(solver, kimberly_busy)

# Megan has no meetings (no busy intervals).

# Marie's busy intervals:
#   10:00 to 11:00 -> [600, 660)
#   11:30 to 15:00 -> [690, 900)
#   16:00 to 16:30 -> [960, 990)
marie_busy = [(600, 660), (690, 900), (960, 990)]
add_busy_constraints(solver, marie_busy)

# Diana's busy intervals:
#    9:30 to 10:00 -> [570, 600)
#   10:30 to 14:30 -> [630, 870)
#   15:30 to 17:00 -> [930, 1020)
diana_busy = [(570, 600), (630, 870), (930, 1020)]
add_busy_constraints(solver, diana_busy)

# We want the meeting to occur at the earliest available time.
solution_found = False
# Search possible start times from 10:00 (600) up to the latest possible start (1020 - duration = 990).
for t in range(600, 991):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")