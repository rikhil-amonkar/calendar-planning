from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time (in minutes since midnight)

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy time intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish at or before b_start,
        # or start at or after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Andrew's busy intervals:
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 14:00 -> [810, 840)
andrew_busy = [(690, 780), (810, 840)]
add_busy_constraints(solver, andrew_busy)

# Keith's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
keith_busy = [(720, 750), (810, 840), (930, 960), (990, 1020)]
add_busy_constraints(solver, keith_busy)

# Pamela's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
pamela_busy = [(570, 600), (750, 780), (810, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, pamela_busy)

# Carol's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 11:00 to 12:30 -> [660, 750)
# 14:30 to 15:30 -> [870, 930)
carol_busy = [(540, 570), (660, 750), (870, 930)]
add_busy_constraints(solver, carol_busy)

# Barbara's busy intervals:
# 9:00 to 13:00  -> [540, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
barbara_busy = [(540, 780), (840, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, barbara_busy)

# Ronald's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 16:00 -> [750, 960)
# 16:30 to 17:00 -> [990, 1020)
ronald_busy = [(540, 570), (600, 630), (750, 960), (990, 1020)]
add_busy_constraints(solver, ronald_busy)

# Diana's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 16:00 -> [780, 960)
diana_busy = [(540, 570), (600, 630), (660, 690), (720, 750), (780, 960)]
add_busy_constraints(solver, diana_busy)

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