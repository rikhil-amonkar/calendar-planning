from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Alan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:30 -> [660, 750)
# 14:00 to 14:30 -> [840, 870)
alan_busy = [(540, 570), (600, 630), (660, 750), (840, 870)]
add_busy_constraints(solver, alan_busy)

# Michael is free all day, so no constraints.

# Michelle is free all day, so no constraints.

# Roy's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:30  -> [810, 870)
roy_busy = [(570, 600), (750, 780), (810, 870)]
add_busy_constraints(solver, roy_busy)

# Judy's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 15:30  -> [660, 930)
# 16:00 to 17:00  -> [960, 1020)
judy_busy = [(540, 630), (660, 930), (960, 1020)]
add_busy_constraints(solver, judy_busy)

# Natalie's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 12:30  -> [660, 750)
# 13:00 to 17:00  -> [780, 1020)
natalie_busy = [(540, 570), (660, 750), (780, 1020)]
add_busy_constraints(solver, natalie_busy)

# Brian's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 12:00  -> [660, 720)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
brian_busy = [(570, 630), (660, 720), (810, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, brian_busy)

# Search for a valid meeting time by iterating through possible start times.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the previous state.
        break
    solver.pop()  # Restore if this candidate did not work.

if not found:
    print("No valid meeting time could be found.")