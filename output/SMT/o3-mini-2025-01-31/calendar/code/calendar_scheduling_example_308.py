from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that ensure the meeting does not overlap a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting does not overlap a busy interval if it finishes before the interval starts
        # or starts at or after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Adam's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   12:30 to 13:00 -> [750, 780)
adam_busy = [(600, 630), (750, 780)]
add_busy_constraints(solver, adam_busy)

# Frances's busy intervals:
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 14:30 -> [840, 870)
frances_busy = [(750, 780), (840, 870)]
add_busy_constraints(solver, frances_busy)

# Natalie's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   12:30 to 13:30 -> [750, 810)
#   16:00 to 16:30 -> [960, 990)
natalie_busy = [(630, 660), (750, 810), (960, 990)]
add_busy_constraints(solver, natalie_busy)

# Patrick's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   12:00 to 14:00 -> [720, 840)
#   14:30 to 16:00 -> [870, 960)
patrick_busy = [(630, 660), (720, 840), (870, 960)]
add_busy_constraints(solver, patrick_busy)

# Willie's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:30  -> [630, 690)
#   12:00 to 13:00  -> [720, 780)
#   14:00 to 15:30  -> [840, 930)
#   16:00 to 16:30  -> [960, 990)
willie_busy = [(540, 600), (630, 690), (720, 780), (840, 930), (960, 990)]
add_busy_constraints(solver, willie_busy)

# Diana's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 16:30 -> [660, 990)
diana_busy = [(540, 630), (660, 990)]
add_busy_constraints(solver, diana_busy)

# Now, search for an earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # t ranges from 540 to 990 inclusive
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