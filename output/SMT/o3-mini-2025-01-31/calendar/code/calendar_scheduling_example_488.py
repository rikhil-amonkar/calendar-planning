from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes since midnight)

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy-time constraints for a participant.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval
        # starts or start after it ends:
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Samuel is free the entire day, no constraints needed.

# Maria's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 13:30 to 14:00   -> [810, 840)
# 16:30 to 17:00   -> [990, 1020)
maria_busy = [(540, 600), (810, 840), (990, 1020)]
add_busy_constraints(solver, maria_busy)

# Bryan's busy intervals:
# 9:00 to 9:30     -> [540, 570)
# 16:00 to 16:30   -> [960, 990)
bryan_busy = [(540, 570), (960, 990)]
add_busy_constraints(solver, bryan_busy)

# Kyle's busy intervals:
# 10:00 to 10:30   -> [600, 630)
# 11:00 to 12:00   -> [660, 720)
# 14:00 to 14:30   -> [840, 870)
# 15:00 to 15:30   -> [900, 930)
# 16:30 to 17:00   -> [990, 1020)
kyle_busy = [(600, 630), (660, 720), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, kyle_busy)

# Christina's busy intervals:
# 9:00 to 10:30    -> [540, 630)
# 11:00 to 11:30   -> [660, 690)
# 12:00 to 15:00   -> [720, 900)
# 15:30 to 16:00   -> [930, 960)
# 16:30 to 17:00   -> [990, 1020)
christina_busy = [(540, 630), (660, 690), (720, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, christina_busy)

# Virginia's busy intervals:
# 9:00 to 9:30     -> [540, 570)
# 10:00 to 10:30   -> [600, 630)
# 11:00 to 11:30   -> [660, 690)
# 12:00 to 15:00   -> [720, 900)
# 15:30 to 17:00   -> [930, 1020)
virginia_busy = [(540, 570), (600, 630), (660, 690), (720, 900), (930, 1020)]
add_busy_constraints(solver, virginia_busy)

# Ann's busy intervals:
# 9:00 to 10:30    -> [540, 630)
# 11:30 to 17:00   -> [690, 1020)
ann_busy = [(540, 630), (690, 1020)]
add_busy_constraints(solver, ann_busy)

# Search for the earliest valid 30-minute meeting time.
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