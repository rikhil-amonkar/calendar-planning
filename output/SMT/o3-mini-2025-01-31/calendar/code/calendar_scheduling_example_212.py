from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, because Charles does not want a meeting after 16:00,
# the meeting must finish by 16:00 (960 minutes).
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours and satisfy Charles' preference.
solver.add(start >= 540, start + duration <= 960)

# Helper function: for each busy interval [busy_start, busy_end),
# the meeting [start, start+duration) must not overlap with that interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Katherine's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 11:30 to 12:00  -> [690, 720)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
katherine_busy = [(540, 570), (600, 660), (690, 720), (810, 840), (870, 900)]
add_busy_constraints(solver, katherine_busy)

# Carl's busy intervals:
# 10:30 to 11:30 -> [630, 690)
carl_busy = [(630, 690)]
add_busy_constraints(solver, carl_busy)

# Charles's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:30 -> [750, 810)
# 14:30 to 15:30 -> [870, 930)
charles_busy = [(600, 630), (660, 690), (750, 810), (870, 930)]
add_busy_constraints(solver, charles_busy)

# Gerald's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:30 -> [600, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
gerald_busy = [(540, 570), (600, 750), (780, 810), (870, 900)]
add_busy_constraints(solver, gerald_busy)

# Stephanie's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:00 -> [630, 720)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 16:00 -> [900, 960)
stephanie_busy = [(540, 570), (630, 720), (780, 840), (900, 960)]
add_busy_constraints(solver, stephanie_busy)

# Find the earliest valid meeting time.
solution_found = False
# The latest valid start time is 960 - duration = 930.
for t in range(540, 931):
    solver.push()  # Save current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")