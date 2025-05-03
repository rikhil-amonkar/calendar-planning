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

# Helper function to ensure the meeting does not overlap with any busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Theresa's busy intervals:
# 9:30 to 10:30 -> [570, 630)
# 15:00 to 16:00 -> [900, 960)
theresa_busy = [(570, 630), (900, 960)]
add_busy_constraints(solver, theresa_busy)

# Alexander's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
alexander_busy = [(720, 750), (810, 840)]
add_busy_constraints(solver, alexander_busy)

# Virginia is free all day, so no busy intervals.

# Lisa's busy intervals:
# 10:30 to 12:30 -> [630, 750)
# 13:30 to 14:30 -> [810, 870)
# 16:00 to 17:00 -> [960, 1020)
lisa_busy = [(630, 750), (810, 870), (960, 1020)]
add_busy_constraints(solver, lisa_busy)

# Natalie's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:30 -> [660, 750)
# 13:30 to 15:30 -> [810, 930)
# 16:00 to 17:00 -> [960, 1020)
natalie_busy = [(540, 570), (660, 750), (810, 930), (960, 1020)]
add_busy_constraints(solver, natalie_busy)

# Victoria's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 12:30  -> [660, 750)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 16:30  -> [900, 990)
victoria_busy = [(570, 630), (660, 750), (810, 870), (900, 990)]
add_busy_constraints(solver, victoria_busy)

# Search for the earliest meeting start time that satisfies all constraints.
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