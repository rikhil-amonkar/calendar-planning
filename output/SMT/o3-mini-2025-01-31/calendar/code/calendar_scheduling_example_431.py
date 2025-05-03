from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, William prefers not to meet before 9:30 (570 minutes).
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Enforce work hours and William's preference.
solver.add(start >= 570, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts or
        # begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Dylan, William, Douglas, and Kimberly are free the entire day (William's constraint is already applied).

# Emma's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 12:00  -> [660, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 16:00  -> [840, 960)
# 16:30 to 17:00  -> [990, 1020)
emma_busy = [(570, 630), (660, 720), (750, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, emma_busy)

# Alan's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 17:00  -> [660, 1020)
alan_busy = [(570, 630), (660, 1020)]
add_busy_constraints(solver, alan_busy)

# Philip's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 12:30  -> [660, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 16:30  -> [960, 990)
philip_busy = [(570, 630), (660, 750), (780, 810), (870, 900), (960, 990)]
add_busy_constraints(solver, philip_busy)

# Iterate over possible start times within the allowed range to find a valid meeting slot.
found = False
for t in range(570, 1020 - duration + 1):  # starting at 9:30 (570) to latest start time
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")