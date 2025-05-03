from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday are 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints ensuring the meeting does not overlap a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting does not overlap with the interval [bs, be) if either:
        #  - it ends on or before bs, or
        #  - it starts on or after be.
        s.add(Or(start + duration <= bs, start >= be))

# Jason's blocked intervals:
#   9:30 to 10:00  → [570, 600)
#   10:30 to 11:30 → [630, 690)
#   12:30 to 13:00 → [750, 780)
#   14:00 to 14:30 → [840, 870)
#   16:00 to 16:30 → [960, 990)
jason_busy = [(570, 600), (630, 690), (750, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, jason_busy)

# Anthony's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 11:00 → [600, 660)
#   15:30 to 17:00 → [930, 1020)
anthony_busy = [(540, 570), (600, 660), (930, 1020)]
add_busy_constraints(solver, anthony_busy)

# Joan's blocked intervals:
#   11:00 to 11:30 → [660, 690)
#   12:00 to 12:30 → [720, 750)
#   15:00 to 15:30 → [900, 930)
#   16:00 to 16:30 → [960, 990)
joan_busy = [(660, 690), (720, 750), (900, 930), (960, 990)]
add_busy_constraints(solver, joan_busy)

# Elizabeth's busy intervals:
#   9:00 to 11:00   → [540, 660)
#   11:30 to 12:00  → [690, 720)
#   12:30 to 13:00  → [750, 780)
#   13:30 to 15:30  → [810, 930)
#   16:00 to 17:00  → [960, 1020)
elizabeth_busy = [(540, 660), (690, 720), (750, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, elizabeth_busy)

# Ryan's meeting intervals:
#   9:00 to 10:00   → [540, 600)
#   11:00 to 11:30  → [660, 690)
#   12:30 to 13:00  → [750, 780)
#   13:30 to 16:30  → [810, 990)
ryan_busy = [(540, 600), (660, 690), (750, 780), (810, 990)]
add_busy_constraints(solver, ryan_busy)

# Jeffrey's blocked intervals:
#   9:30 to 10:30   → [570, 630)
#   11:00 to 11:30  → [660, 690)
#   12:00 to 13:00  → [720, 780)
#   13:30 to 14:00  → [810, 840)
#   14:30 to 16:00  → [870, 960)
#   16:30 to 17:00  → [990, 1020)
jeffrey_busy = [(570, 630), (660, 690), (720, 780), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, jeffrey_busy)

# Search for the earliest valid meeting start time.
found = False
# The meeting can start any time t such that 540 <= t <= 1020 - duration.
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