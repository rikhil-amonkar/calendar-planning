from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so we require: start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting doesn't overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [bs, be), the meeting must end on or before bs, or start on or after be.
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Alice's busy intervals:
#   10:00 to 10:30 -> [600, 630]
#   14:30 to 15:00 -> [870, 900]
#   15:30 to 16:30 -> [930, 990]
alice_busy = [(600, 630), (870, 900), (930, 990)]
add_busy_constraints(solver, alice_busy)

# Charlotte is free all day, thus no busy intervals.

# Stephanie's busy intervals:
#   9:00 to 9:30   -> [540, 570]
#   10:30 to 11:00 -> [630, 660]
#   11:30 to 13:00 -> [690, 780]
#   13:30 to 14:30 -> [810, 870]
#   15:00 to 15:30 -> [900, 930]
stephanie_busy = [(540, 570), (630, 660), (690, 780), (810, 870), (900, 930)]
add_busy_constraints(solver, stephanie_busy)

# Ethan's busy intervals:
#   9:00 to 12:00   -> [540, 720]
#   12:30 to 13:00  -> [750, 780]
#   13:30 to 14:30  -> [810, 870]
#   15:00 to 15:30  -> [900, 930]
#   16:00 to 17:00  -> [960, 1020]
ethan_busy = [(540, 720), (750, 780), (810, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, ethan_busy)

# Find a meeting time that satisfies all constraints by looking for the earliest start time.
# We can instruct Z3 to minimize 'start' by checking sequentially.
# One way is to iterate over all possible minutes from 540 upwards.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        solution_found = True
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
              start_hour, start_min, end_hour, end_min))
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")