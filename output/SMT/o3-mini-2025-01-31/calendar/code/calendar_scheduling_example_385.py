from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes (9:00=540, 17:00=1020) and meeting duration (30 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting must either finish by bs or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Noah's busy intervals:
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:00 -> [780, 840)
#   14:30 to 15:00 -> [870, 900)
noah_busy = [(720, 750), (780, 840), (870, 900)]
add_busy_constraints(solver, noah_busy)

# Jesse's busy intervals:
#   10:30 to 11:30 -> [630, 690)
#   12:30 to 13:00 -> [750, 780)
#   14:00 to 15:00 -> [840, 900)
#   16:00 to 16:30 -> [960, 990)
jesse_busy = [(630, 690), (750, 780), (840, 900), (960, 990)]
add_busy_constraints(solver, jesse_busy)

# Amy's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:00 -> [690, 720)
amy_busy = [(600, 630), (690, 720)]
add_busy_constraints(solver, amy_busy)

# Timothy's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   11:00 to 12:00 -> [660, 720)
#   12:30 to 13:30 -> [750, 810)
#   14:00 to 15:00 -> [840, 900)
#   15:30 to 16:30 -> [930, 990)
timothy_busy = [(570, 630), (660, 720), (750, 810), (840, 900), (930, 990)]
add_busy_constraints(solver, timothy_busy)

# Eugene's busy intervals:
#   9:00 to 11:00  -> [540, 660)
#   13:00 to 14:00 -> [780, 840)
#   15:30 to 16:00 -> [930, 960)
#   16:30 to 17:00 -> [990, 1020)
eugene_busy = [(540, 660), (780, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, eugene_busy)

# Theresa's busy intervals:
#   9:00 to 10:00  -> [540, 600)
#   10:30 to 13:00 -> [630, 780)
#   13:30 to 15:00 -> [810, 900)
#   16:00 to 17:00 -> [960, 1020)
theresa_busy = [(540, 600), (630, 780), (810, 900), (960, 1020)]
add_busy_constraints(solver, theresa_busy)

# We iterate over possible meeting start times minute-by-minute and choose the first valid (earliest) one.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")