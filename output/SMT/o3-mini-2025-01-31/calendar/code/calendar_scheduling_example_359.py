from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 mins) to 17:00 (1020 mins)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy constraints.
# For each busy interval [bs, be), the meeting must either finish on or before bs,
# or start on or after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Bryan's busy intervals:
# 9:00-9:30  => [540, 570)
# 10:00-10:30 => [600, 630)
# 12:30-13:00 => [750, 780)
# 16:00-16:30 => [960, 990)
bryan_busy = [(540, 570), (600, 630), (750, 780), (960, 990)]
add_busy_constraints(solver, bryan_busy)

# Sophia's busy intervals:
# 13:00-13:30 => [780, 810)
# 16:00-16:30 => [960, 990)
sophia_busy = [(780, 810), (960, 990)]
add_busy_constraints(solver, sophia_busy)

# Jeremy is free all day; no constraints needed.

# Marie's busy intervals:
# 9:00-9:30   => [540, 570)
# 10:00-12:00 => [600, 720)
# 13:00-14:00 => [780, 840)
# 15:30-16:00 => [930, 960)
marie_busy = [(540, 570), (600, 720), (780, 840), (930, 960)]
add_busy_constraints(solver, marie_busy)

# Tyler's busy intervals:
# 9:00-10:00   => [540, 600)
# 11:00-11:30  => [660, 690)
# 13:00-14:00  => [780, 840)
# 14:30-17:00  => [870, 1020)
tyler_busy = [(540, 600), (660, 690), (780, 840), (870, 1020)]
add_busy_constraints(solver, tyler_busy)

# Emily's busy intervals:
# 9:00-10:00   => [540, 600)
# 11:00-12:30  => [660, 750)
# 13:30-14:00  => [810, 840)
# 14:30-15:30  => [870, 930)
emily_busy = [(540, 600), (660, 750), (810, 840), (870, 930)]
add_busy_constraints(solver, emily_busy)

# Iterate over all possible starting times to find a valid meeting time.
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