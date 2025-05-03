from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define the meeting parameters: working hours (9:00 = 540 to 17:00 = 1020) and meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting must either end before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Jason's calendar is wide open, so no constraints.

# Christopher has no meetings, so no constraints.

# Katherine's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 13:30 -> [750, 810)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
katherine_busy = [(600, 630), (660, 690), (750, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, katherine_busy)

# Justin's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:00 to 12:00 -> [660, 720)
#   12:30 to 13:30 -> [750, 810)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:30 -> [930, 990)
justin_busy = [(540, 630), (660, 720), (750, 810), (870, 900), (930, 990)]
add_busy_constraints(solver, justin_busy)

# Abigail's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   12:30 to 15:00 -> [750, 900)
#   15:30 to 16:30 -> [930, 990)
abigail_busy = [(630, 660), (750, 900), (930, 990)]
add_busy_constraints(solver, abigail_busy)

# Kayla's busy intervals:
#   9:30 to 10:00  -> [570, 600)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 14:00 -> [750, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:30 -> [930, 990)
kayla_busy = [(570, 600), (690, 720), (750, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, kayla_busy)

# Search for the earliest valid meeting time by iterating minute-by-minute within working hours.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()   # Save the current state of the solver.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()  # Restore solver state.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")