from z3 import *

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Monday work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to take place within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(s, busy_intervals):
    # For each busy interval [bs, be), ensure that either the meeting ends
    # before the interval starts, or starts after the interval ends.
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Stephanie's busy intervals:
#   9:00 to 9:30  → [540, 570)
#   10:30 to 11:00 → [630, 660)
#   11:30 to 12:30 → [690, 750)
stephanie_busy = [(540, 570), (630, 660), (690, 750)]
add_busy_constraints(solver, stephanie_busy)

# Henry's busy intervals:
#   11:00 to 12:30 → [660, 750)
#   14:00 to 14:30 → [840, 870)
henry_busy = [(660, 750), (840, 870)]
add_busy_constraints(solver, henry_busy)

# Janice's busy intervals:
#   9:30 to 10:30  → [570, 630)
#   14:30 to 15:00 → [870, 900)
#   15:30 to 16:00 → [930, 960)
janice_busy = [(570, 630), (870, 900), (930, 960)]
add_busy_constraints(solver, janice_busy)

# Judy's busy intervals:
#   9:00 to 10:00  → [540, 600)
#   10:30 to 12:00 → [630, 720)
#   13:00 to 13:30 → [780, 810)
#   14:00 to 15:00 → [840, 900)
judy_busy = [(540, 600), (630, 720), (780, 810), (840, 900)]
add_busy_constraints(solver, judy_busy)

# Victoria's busy intervals:
#   10:00 to 10:30 → [600, 630)
#   12:00 to 13:30 → [720, 810)
#   14:00 to 15:30 → [840, 930)
#   16:00 to 16:30 → [960, 990)
victoria_busy = [(600, 630), (720, 810), (840, 930), (960, 990)]
add_busy_constraints(solver, victoria_busy)

# Joe's busy intervals:
#   9:00 to 10:30  → [540, 630)
#   11:00 to 12:00 → [660, 720)
#   12:30 to 15:30 → [750, 930)
#   16:00 to 16:30 → [960, 990)
joe_busy = [(540, 630), (660, 720), (750, 930), (960, 990)]
add_busy_constraints(solver, joe_busy)

# Search for the earliest valid meeting time.
found = False

# The meeting can start as early as 9:00 (540 minutes).
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current solver state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore state after finding a solution
        break
    solver.pop()  # Restore state if no solution for this time

if not found:
    print("No valid meeting time could be found.")