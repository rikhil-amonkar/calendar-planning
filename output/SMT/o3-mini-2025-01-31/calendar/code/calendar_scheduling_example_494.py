from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy-time constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Denise's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
denise_busy = [(630, 660), (690, 720)]
add_busy_constraints(solver, denise_busy)

# Roy's busy intervals:
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
roy_busy = [(840, 870), (990, 1020)]
add_busy_constraints(solver, roy_busy)

# Roger is free the entire day, so no constraints.

# Debra's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
debra_busy = [(600, 660), (840, 870), (960, 990)]
add_busy_constraints(solver, debra_busy)

# David's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
david_busy = [(540, 570), (600, 690), (720, 750), (780, 810), (870, 900), (990, 1020)]
add_busy_constraints(solver, david_busy)

# Danielle's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 10:30  -> [600, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 15:00  -> [840, 900)
# 15:30 to 17:00  -> [930, 1020)
danielle_busy = [(540, 570), (600, 630), (660, 690), (750, 810), (840, 900), (930, 1020)]
add_busy_constraints(solver, danielle_busy)

# Brian's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 14:30  -> [690, 870)
# 16:00 to 17:00  -> [960, 1020)
brian_busy = [(540, 660), (690, 870), (960, 1020)]
add_busy_constraints(solver, brian_busy)

# Search for the earliest valid 30-minute meeting time.
found = False
for t in range(540, 1020 - duration + 1):  # iterate possible start times in minutes
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")