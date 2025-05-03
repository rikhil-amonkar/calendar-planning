from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting [start, start+duration) must not overlap: 
    # i.e., it must end before busy_start, or start on/after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Julia's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
julia_busy = [(630, 690), (720, 750), (780, 810), (840, 870), (900, 930)]
add_busy_constraints(solver, julia_busy)

# Joshua is free all day, so no busy intervals.

# Nicholas's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 15:30 to 16:30 -> [930, 990)
nicholas_busy = [(540, 570), (720, 750), (930, 990)]
add_busy_constraints(solver, nicholas_busy)

# David's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
# 16:00 to 17:00 -> [960, 1020)
david_busy = [(540, 660), (720, 750), (780, 810), (840, 900), (960, 1020)]
add_busy_constraints(solver, david_busy)

# Melissa's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 17:00 -> [930, 1020)
melissa_busy = [(540, 570), (750, 780), (810, 900), (930, 1020)]
add_busy_constraints(solver, melissa_busy)

# Search for a valid meeting start time.
solution_found = False
# The latest permissible start is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state before breaking out.
        break
    solver.pop()  # Restore state to try next candidate.

if not solution_found:
    print("No valid meeting time could be found.")