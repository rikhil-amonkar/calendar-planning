from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 = 540 and 17:00 = 1020, and the meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# The meeting must be entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Bryan's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   12:30 to 13:00 -> [750, 780)
bryan_busy = [(600, 630), (750, 780)]
add_busy_constraints(solver, bryan_busy)

# Billy has no meetings, so no constraints.

# Alexander has no meetings, so no constraints.

# Sophia's busy intervals:
#   9:00 to 13:00   -> [540, 780)
#   13:30 to 14:30  -> [810, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 16:30  -> [960, 990)
sophia_busy = [(540, 780), (810, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, sophia_busy)

# Larry's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 13:00  -> [750, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 15:30  -> [870, 930)
#   16:30 to 17:00  -> [990, 1020)
larry_busy = [(540, 570), (630, 690), (750, 780), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, larry_busy)

# Nicole's busy intervals:
#   9:30 to 14:00   -> [570, 840)
#   14:30 to 15:00  -> [870, 900)
nicole_busy = [(570, 840), (870, 900)]
add_busy_constraints(solver, nicole_busy)

# Iterate minute-by-minute to find the earliest meeting time that satisfies all constraints.
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