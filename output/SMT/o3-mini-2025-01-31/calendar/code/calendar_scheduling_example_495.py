from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Define work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
meeting_duration = 30  # in minutes
start = Int("start")   # meeting start time in minutes since midnight

# Constrain the meeting to fall within the work day.
solver.add(start >= 540, start + meeting_duration <= 1020)

# Helper function to add busy intervals constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # For each busy interval, the meeting [start, start+meeting_duration) must not overlap.
        solver.add(Or(start + meeting_duration <= b_start, start >= b_end))

# Participant busy schedules:

# Jordan's busy intervals:
# 10:00 to 11:00   -> [600, 660)
# 11:30 to 12:00   -> [690, 720)
# 13:00 to 13:30   -> [780, 810)
# 14:30 to 15:00   -> [870, 900)
# 16:00 to 16:30   -> [960, 990)
jordan_busy = [(600, 660), (690, 720), (780, 810), (870, 900), (960, 990)]
add_busy_constraints(solver, jordan_busy)

# Ralph's busy intervals:
# 12:30 to 13:00   -> [750, 780)
# 14:00 to 14:30   -> [840, 870)
ralph_busy = [(750, 780), (840, 870)]
add_busy_constraints(solver, ralph_busy)

# Kathryn's calendar is free; no constraints.

# Isabella's busy intervals:
# 12:30 to 13:00   -> [750, 780)
# 14:00 to 14:30   -> [840, 870)
# 15:30 to 16:30   -> [930, 990)
isabella_busy = [(750, 780), (840, 870), (930, 990)]
add_busy_constraints(solver, isabella_busy)

# Roger's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:00  -> [600, 660)
# 12:30 to 17:00  -> [750, 1020)
roger_busy = [(540, 570), (600, 660), (750, 1020)]
add_busy_constraints(solver, roger_busy)

# Henry's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 13:00  -> [600, 780)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:30  -> [930, 990)
henry_busy = [(540, 570), (600, 780), (810, 900), (930, 990)]
add_busy_constraints(solver, henry_busy)

# Anthony's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 13:00  -> [630, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:00 to 16:30  -> [900, 990)
anthony_busy = [(540, 570), (630, 780), (810, 840), (900, 990)]
add_busy_constraints(solver, anthony_busy)

# Search for earliest valid 30-minute meeting time that satisfies all constraints.
found = False
for t in range(540, 1020 - meeting_duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + meeting_duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")