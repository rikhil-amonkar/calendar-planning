from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap a busy interval if it ends by the time the interval starts,
        # or starts after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Carl's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   15:30 to 16:00 -> [930, 960)
carl_busy = [(600, 630), (930, 960)]
add_busy_constraints(solver, carl_busy)

# Shirley's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   12:00 to 12:30 -> [720, 750)
#   14:00 to 15:30 -> [840, 930)
shirley_busy = [(570, 630), (720, 750), (840, 930)]
add_busy_constraints(solver, shirley_busy)

# Timothy's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   11:30 to 12:00 -> [690, 720)
timothy_busy = [(540, 630), (690, 720)]
add_busy_constraints(solver, timothy_busy)

# Marilyn's busy intervals:
#   9:00 to 11:30  -> [540, 690)
#   12:00 to 13:00 -> [720, 780)
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 16:30 -> [870, 990)
marilyn_busy = [(540, 690), (720, 780), (810, 840), (870, 990)]
add_busy_constraints(solver, marilyn_busy)

# Martha's busy intervals:
#   9:00 to 10:30  -> [540, 630)
#   13:00 to 15:00 -> [780, 900)
#   15:30 to 16:00 -> [930, 960)
martha_busy = [(540, 630), (780, 900), (930, 960)]
add_busy_constraints(solver, martha_busy)

# Samantha's busy intervals:
#   9:00 to 11:00  -> [540, 660)
#   12:00 to 15:00 -> [720, 900)
#   15:30 to 16:30 -> [930, 990)
samantha_busy = [(540, 660), (720, 900), (930, 990)]
add_busy_constraints(solver, samantha_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")