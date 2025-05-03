from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Randy's preference: he would rather not meet after 10:30.
# We add a preference constraint to schedule the meeting at (or before) 10:30.
# (10:30 is 630 minutes from midnight.)
solver.add(start <= 630)

# Helper function: given busy intervals [bs, be) (in minutes), 
# ensure that the meeting does not overlap the interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Diana: free all day, no busy intervals.

# Sean: free all day, no busy intervals.

# Rebecca's busy intervals:
#   13:00 to 13:30 -> [780, 810)
#   16:30 to 17:00 -> [990, 1020)
rebecca_busy = [(780, 810), (990, 1020)]
add_busy_constraints(solver, rebecca_busy)

# Peter's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:30 to 11:30  -> [630, 690)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 16:00  -> [900, 960)
#   16:30 to 17:00  -> [990, 1020)
peter_busy = [(540,570), (630,690), (750,780), (840,870), (900,960), (990,1020)]
add_busy_constraints(solver, peter_busy)

# Lawrence's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 11:00  -> [600, 660)
#   12:00 to 13:00  -> [720, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 15:00  -> [870, 900)
#   16:30 to 17:00  -> [990, 1020)
lawrence_busy = [(540,570), (600,660), (720,780), (810,840), (870,900), (990,1020)]
add_busy_constraints(solver, lawrence_busy)

# Randy's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 11:30  -> [600, 690)
#   12:00 to 13:00  -> [720, 780)
#   13:30 to 15:30  -> [810, 930)
#   16:00 to 17:00  -> [960, 1020)
randy_busy = [(540,570), (600,690), (720,780), (810,930), (960,1020)]
add_busy_constraints(solver, randy_busy)

# Now, iterate minute-by-minute to find a valid meeting time.
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