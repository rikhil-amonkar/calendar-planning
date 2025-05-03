from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints for a participant.
# For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for (bs, be) in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Patrick's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   15:00 to 15:30 -> [900, 930)
patrick_busy = [(690, 720), (900, 930)]
add_busy_constraints(solver, patrick_busy)

# John's busy intervals:
#   11:30 to 12:30 -> [690, 750)
#   13:00 to 14:00 -> [780, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:00 -> [930, 960)
john_busy = [(690, 750), (780, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, john_busy)

# Samantha's busy intervals:
#   12:00 to 12:30 -> [720, 750)
#   16:30 to 17:00 -> [990, 1020)
samantha_busy = [(720, 750), (990, 1020)]
add_busy_constraints(solver, samantha_busy)

# Billy's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00  -> [600, 660)
#   12:30 to 14:00  -> [750, 840)
#   15:30 to 16:00  -> [930, 960)
#   16:30 to 17:00  -> [990, 1020)
billy_busy = [(540, 570), (600, 660), (750, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, billy_busy)

# Christine's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 14:00  -> [630, 840)
#   15:00 to 15:30  -> [900, 930)
christine_busy = [(540, 600), (630, 840), (900, 930)]
add_busy_constraints(solver, christine_busy)

# Ruth's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 16:00  -> [750, 960)
#   16:30 to 17:00  -> [990, 1020)
ruth_busy = [(540, 600), (630, 660), (690, 720), (750, 960), (990, 1020)]
add_busy_constraints(solver, ruth_busy)

# Iterate over possible start times within the work day to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")