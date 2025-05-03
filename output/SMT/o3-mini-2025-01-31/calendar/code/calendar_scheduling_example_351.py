from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must start and end within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting must either finish before bs or start at/after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Andrew's busy intervals:
#   9:00 to 10:30 -> [540, 630)
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 13:00 -> [750, 780)
#   16:30 to 17:00 -> [990, 1020)
andrew_busy = [(540, 630), (660, 690), (750, 780), (990, 1020)]
add_busy_constraints(solver, andrew_busy)

# Rebecca's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   15:30 to 16:00 -> [930, 960)
rebecca_busy = [(630, 660), (930, 960)]
add_busy_constraints(solver, rebecca_busy)

# Harold's busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   15:30 to 16:00 -> [930, 960)
harold_busy = [(540, 570), (930, 960)]
add_busy_constraints(solver, harold_busy)

# Douglas's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 13:00  -> [690, 780)
#   14:00 to 15:00  -> [840, 900)
#   15:30 to 17:00  -> [930, 1020)
douglas_busy = [(540, 660), (690, 780), (840, 900), (930, 1020)]
add_busy_constraints(solver, douglas_busy)

# Jean's busy intervals:
#   9:00 to 11:30   -> [540, 690)
#   13:30 to 16:00  -> [810, 960)
jean_busy = [(540, 690), (810, 960)]
add_busy_constraints(solver, jean_busy)

# Larry's busy intervals:
#   9:30 to 10:30   -> [570, 630)
#   11:00 to 13:00  -> [660, 780)
#   13:30 to 16:30  -> [810, 990)
larry_busy = [(570, 630), (660, 780), (810, 990)]
add_busy_constraints(solver, larry_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the state before breaking.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")