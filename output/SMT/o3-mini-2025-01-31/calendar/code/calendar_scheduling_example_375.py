from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours are 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes from midnight

# The meeting must be scheduled within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function that, given busy intervals (each as [bs, be)), adds constraints that
# the meeting must either end by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Julie's busy intervals:
#   12:00 to 12:30  -> [720, 750)
#   13:30 to 14:00  -> [810, 840)
#   15:00 to 16:00  -> [900, 960)
julie_busy = [(720, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, julie_busy)

# Sara's busy intervals:
#   11:00 to 11:30  -> [660, 690)
#   15:00 to 15:30  -> [900, 930)
sara_busy = [(660, 690), (900, 930)]
add_busy_constraints(solver, sara_busy)

# Donna's busy intervals:
#   10:30 to 11:00  -> [630, 660)
#   12:30 to 13:30  -> [750, 810)
#   14:30 to 15:00  -> [870, 900)
donna_busy = [(630, 660), (750, 810), (870, 900)]
add_busy_constraints(solver, donna_busy)

# Keith's busy intervals:
#   9:00 to 16:00   -> [540, 960)
keith_busy = [(540, 960)]
add_busy_constraints(solver, keith_busy)

# Dylan's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 10:30  -> [600, 630)
#   11:00 to 12:30  -> [660, 750)
#   13:30 to 16:00  -> [810, 960)
dylan_busy = [(540, 570), (600, 630), (660, 750), (810, 960)]
add_busy_constraints(solver, dylan_busy)

# Jose's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   12:00 to 14:30  -> [720, 870)
#   15:30 to 16:30  -> [930, 990)
jose_busy = [(540, 630), (720, 870), (930, 990)]
add_busy_constraints(solver, jose_busy)

# Iterate over possible start times (minute by minute) within the work period.
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