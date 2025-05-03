from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for each busy interval [bs, be), the meeting must either finish by bs or start at or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Mark's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   12:30 to 13:30 -> [750, 810)
#   16:00 to 16:30 -> [960, 990)
mark_busy = [(660, 690), (750, 810), (960, 990)]
add_busy_constraints(solver, mark_busy)

# Logan's busy intervals:
#   11:30 to 12:00 -> [690, 720)
#   13:00 to 13:30 -> [780, 810)
logan_busy = [(690, 720), (780, 810)]
add_busy_constraints(solver, logan_busy)

# Isabella's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:00 to 11:30 -> [660, 690)
isabella_busy = [(540, 570), (660, 690)]
add_busy_constraints(solver, isabella_busy)

# Nathan's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 13:00 -> [600, 780)
#   13:30 to 14:30 -> [810, 870)
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 17:00 -> [960, 1020)
nathan_busy = [(540, 570), (600, 780), (810, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, nathan_busy)

# Anna's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   11:00 to 13:00  -> [660, 780)
#   13:30 to 14:00  -> [810, 840)
#   16:30 to 17:00  -> [990, 1020)
anna_busy = [(540, 600), (660, 780), (810, 840), (990, 1020)]
add_busy_constraints(solver, anna_busy)

# Dylan's busy intervals:
#   9:00 to 9:30    -> [540, 570)
#   10:00 to 10:30  -> [600, 630)
#   11:00 to 12:30  -> [660, 750)
#   13:00 to 14:30  -> [780, 870)
#   15:00 to 16:00  -> [900, 960)
dylan_busy = [(540, 570), (600, 630), (660, 750), (780, 870), (900, 960)]
add_busy_constraints(solver, dylan_busy)

# Iterate over possible start times (minute by minute) within the valid range and check for a solution.
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