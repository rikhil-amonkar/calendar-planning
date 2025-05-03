from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain meeting time to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlapping a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap with a busy interval if it ends before the interval starts 
        # (start + duration <= bs) or starts at/after the busy interval ends (start >= be).
        s.add(Or(start + duration <= bs, start >= be))

# Donald's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:00 to 12:30 -> [660, 750)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
donald_busy = [(570, 600), (660, 750), (870, 900), (990, 1020)]
add_busy_constraints(solver, donald_busy)

# Zachary's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:00 -> [780, 840)
zachary_busy = [(540, 570), (630, 690), (720, 750), (780, 840)]
add_busy_constraints(solver, zachary_busy)

# Kathryn's calendar is wide open, so no busy intervals.

# Deborah's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 17:00 -> [840, 1020)
deborah_busy = [(540, 570), (600, 630), (690, 720), (780, 810), (840, 1020)]
add_busy_constraints(solver, deborah_busy)

# Teresa's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
teresa_busy = [(540, 570), (600, 660), (690, 750), (840, 870), (900, 960)]
add_busy_constraints(solver, teresa_busy)

# James's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 17:00 -> [870, 1020)
james_busy = [(570, 630), (660, 750), (780, 840), (870, 1020)]
add_busy_constraints(solver, james_busy)

# Now, we search for an earliest meeting start time that satisfies all constraints.
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