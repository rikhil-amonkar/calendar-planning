from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Diane would like to avoid more meetings on Monday after 15:30.
# We'll require that the meeting ends by 15:30 (i.e., start + duration <= 930).
solver.add(start + duration <= 930)

# Helper function to add constraints ensuring that the meeting does not overlap with busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap a busy interval if it ends before the interval starts,
        # or begins at or after the interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Diane's calendar is wide open (no busy intervals).

# Helen has no meetings the whole day.
# Arthur has no meetings the whole day.

# Ethan's busy intervals:
#    9:00 to 9:30   -> [540, 570)
#    10:00 to 10:30 -> [600, 630)
#    11:00 to 12:30 -> [660, 750)
#    13:30 to 15:00 -> [810, 900)
ethan_busy = [(540, 570), (600, 630), (660, 750), (810, 900)]
add_busy_constraints(solver, ethan_busy)

# Beverly's busy intervals:
#    9:00 to 10:00   -> [540, 600)
#    10:30 to 11:00  -> [630, 660)
#    11:30 to 12:30  -> [690, 750)
#    13:30 to 15:30  -> [810, 930)
#    16:30 to 17:00  -> [990, 1020)
beverly_busy = [(540, 600), (630, 660), (690, 750), (810, 930), (990, 1020)]
add_busy_constraints(solver, beverly_busy)

# Deborah's busy intervals:
#    9:00 to 11:00   -> [540, 660)
#    12:30 to 13:00  -> [750, 780)
#    13:30 to 14:30  -> [810, 870)
#    15:00 to 15:30  -> [900, 930)
#    16:00 to 17:00  -> [960, 1020)
deborah_busy = [(540, 660), (750, 780), (810, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, deborah_busy)

# Now, we search for an earliest meeting start time that satisfies all constraints.
found = False
# Due to Diane's preference (meeting must end by 15:30), t can be at most 900.
for t in range(540, 901):
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