from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) should either finish before a busy interval starts
        # or begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Kyle is free the entire day: no constraints.

# Kathleen's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
kathleen_busy = [(600, 630), (750, 780), (840, 870), (930, 960)]
add_busy_constraints(solver, kathleen_busy)

# Ashley's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 15:30 to 16:30 -> [930, 990)
ashley_busy = [(540, 570), (720, 750), (930, 990)]
add_busy_constraints(solver, ashley_busy)

# Christian's busy intervals:
# 9:00 to 13:00   -> [540, 780)
# 13:30 to 15:00  -> [810, 900)
# 16:30 to 17:00  -> [990, 1020)
christian_busy = [(540, 780), (810, 900), (990, 1020)]
add_busy_constraints(solver, christian_busy)

# Matthew's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 13:00  -> [630, 780)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
matthew_busy = [(540, 600), (630, 780), (810, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, matthew_busy)

# Search for the earliest valid meeting time satisfying all constraints.
solution_found = False
# The latest valid start is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save state for backtracking.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")