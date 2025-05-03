from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight.

# Constrain meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap a busy interval if it ends by the time that the busy interval begins,
        # or starts after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Jacob's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 12:30 -> [720, 750)
#   13:30 to 14:00 -> [810, 840)
#   16:00 to 16:30 -> [960, 990)
jacob_busy = [(540, 570), (600, 660), (720, 750), (810, 840), (960, 990)]
add_busy_constraints(solver, jacob_busy)

# Nancy's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   14:30 to 16:00 -> [870, 960)
nancy_busy = [(660, 690), (870, 960)]
add_busy_constraints(solver, nancy_busy)

# Lori's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 11:30 -> [660, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:30 to 14:00 -> [810, 840)
lori_busy = [(540, 570), (660, 690), (720, 750), (810, 840)]
add_busy_constraints(solver, lori_busy)

# Ann's busy intervals:
#   10:00 to 13:00 -> [600, 780)
#   14:30 to 16:30 -> [870, 990)
ann_busy = [(600, 780), (870, 990)]
add_busy_constraints(solver, ann_busy)

# Pamela's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:30 -> [630, 690)
#   12:00 to 12:30 -> [720, 750)
#   13:30 to 15:00 -> [810, 900)
#   15:30 to 16:00 -> [930, 960)
pamela_busy = [(540, 570), (630, 690), (720, 750), (810, 900), (930, 960)]
add_busy_constraints(solver, pamela_busy)

# Anna's busy intervals:
#   9:30 to 11:30  -> [570, 690)
#   12:00 to 13:00 -> [720, 780)
#   13:30 to 14:30 -> [810, 870)
#   15:00 to 17:00 -> [900, 1020)
anna_busy = [(570, 690), (720, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, anna_busy)

# Search for the earliest valid meeting start time.
found = False
for t in range(540, 1020 - duration + 1):  # from 9:00 (540) to 16:30 (990)
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