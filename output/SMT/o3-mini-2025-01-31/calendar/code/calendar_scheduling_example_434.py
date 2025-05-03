from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting doesn't overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting interval [start, start+duration) must finish before the busy interval starts,
        # or must start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Kayla's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 15:00 to 15:30 -> [900, 930)
kayla_busy = [(540, 570), (900, 930)]
add_busy_constraints(solver, kayla_busy)

# Karen is free the entire day, so no constraints.

# Henry's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
henry_busy = [(600, 630), (720, 750), (840, 870), (930, 960)]
add_busy_constraints(solver, henry_busy)

# Randy's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 16:30 to 17:00 -> [990, 1020)
randy_busy = [(630, 690), (720, 750), (990, 1020)]
add_busy_constraints(solver, randy_busy)

# Stephanie's busy intervals:
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:30 to 16:30 -> [870, 990)
stephanie_busy = [(600, 690), (720, 810), (870, 990)]
add_busy_constraints(solver, stephanie_busy)

# Tyler's busy intervals:
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 13:30 -> [720, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
tyler_busy = [(600, 690), (720, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, tyler_busy)

# Joe's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 14:30  -> [780, 870)
# 15:00 to 17:00  -> [900, 1020)
joe_busy = [(540, 630), (660, 690), (720, 750), (780, 870), (900, 1020)]
add_busy_constraints(solver, joe_busy)

# Now, search for a valid meeting time by iterating over the allowed minutes.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}.".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")