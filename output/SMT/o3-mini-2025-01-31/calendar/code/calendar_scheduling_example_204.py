from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting interval [start, start+duration)
# must either finish before busy_start or start at or after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Benjamin's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
benjamin_busy = [(600, 630), (690, 720), (750, 780), (810, 840), (900, 930), (960, 990)]
add_busy_constraints(solver, benjamin_busy)

# Juan's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 16:00 -> [870, 960)
juan_busy = [(600, 630), (660, 690), (720, 750), (870, 960)]
add_busy_constraints(solver, juan_busy)

# Heather's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
heather_busy = [(540, 570), (600, 630), (750, 780), (840, 870)]
add_busy_constraints(solver, heather_busy)

# Nathan's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30 -> [690, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
nathan_busy = [(540, 660), (690, 750), (840, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, nathan_busy)

# Jacob's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 13:00 -> [660, 780)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 17:00 -> [930, 1020)
jacob_busy = [(540, 570), (600, 630), (660, 780), (810, 900), (930, 1020)]
add_busy_constraints(solver, jacob_busy)

# Find a valid meeting start time.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current solver state.
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
        solver.pop()  # Restore state before exiting.
        break
    solver.pop()  # Restore state for the next candidate

if not solution_found:
    print("No valid meeting time could be found.")