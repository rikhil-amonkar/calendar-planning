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
        # The meeting does not overlap a busy interval if it finishes before the interval starts,
        # or starts after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Zachary, Douglas, and Adam are free all day (no busy intervals).

# Mark's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 14:00 -> [720, 840)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 16:30 -> [930, 990)
mark_busy = [(540, 570), (630, 690), (720, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, mark_busy)

# Ashley's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:30 -> [600, 690)
#   12:00 to 17:00 -> [720, 1020)
ashley_busy = [(540, 570), (600, 690), (720, 1020)]
add_busy_constraints(solver, ashley_busy)

# Jennifer's busy intervals:
#   9:30 to 10:30  -> [570, 630)
#   12:00 to 12:30  -> [720, 750)
#   13:30 to 14:30  -> [810, 870)
#   15:00 to 15:30  -> [900, 930)
#   16:00 to 17:00  -> [960, 1020)
jennifer_busy = [(570, 630), (720, 750), (810, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, jennifer_busy)

# Now, search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # t from 540 to 990 inclusive
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