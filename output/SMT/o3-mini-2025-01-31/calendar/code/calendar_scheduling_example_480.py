from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time (in minutes since midnight)

# The meeting must occur entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for a participant's busy time intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before b_start
        # or start after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Betty's busy intervals:
# 11:00 to 12:00 -> [660, 720)
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
betty_busy = [(660, 720), (840, 870), (990, 1020)]
add_busy_constraints(solver, betty_busy)

# Roy is free the entire day; no constraints needed.

# Douglas's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 12:00  -> [660, 720)
# 14:00 to 14:30  -> [840, 870)
# 15:30 to 16:30  -> [930, 990)
douglas_busy = [(570, 600), (660, 720), (840, 870), (930, 990)]
add_busy_constraints(solver, douglas_busy)

# Kimberly's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:00 -> [780, 840)
# 16:00 to 16:30 -> [960, 990)
kimberly_busy = [(720, 750), (780, 840), (960, 990)]
add_busy_constraints(solver, kimberly_busy)

# Ashley's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:30 -> [660, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 17:00 -> [930, 1020)
ashley_busy = [(540, 570), (600, 630), (660, 750), (780, 810), (840, 870), (930, 1020)]
add_busy_constraints(solver, ashley_busy)

# Isabella's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:30 to 14:30  -> [810, 870)
# 16:00 to 17:00  -> [960, 1020)
isabella_busy = [(540, 660), (690, 750), (810, 870), (960, 1020)]
add_busy_constraints(solver, isabella_busy)

# Carl's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 17:00 -> [900, 1020)
carl_busy = [(540, 570), (600, 630), (750, 870), (900, 1020)]
add_busy_constraints(solver, carl_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1): 
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