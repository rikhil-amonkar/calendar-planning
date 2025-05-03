from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Represents the meeting start time in minutes since midnight

# Constrain the meeting to be fully within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either end before the busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant busy intervals (times in minutes from midnight):

# Willie is free all day; no constraints needed.

# Scott's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
scott_busy = [(540, 570), (600, 630), (930, 960), (990, 1020)]
add_busy_constraints(solver, scott_busy)

# Jordan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 12:30 -> [720, 750)
# 16:30 to 17:00 -> [990, 1020)
jordan_busy = [(540, 570), (600, 630), (720, 750), (990, 1020)]
add_busy_constraints(solver, jordan_busy)

# Austin's busy intervals:
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
austin_busy = [(690, 780), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, austin_busy)

# Kimberly's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 16:00 -> [900, 960)
kimberly_busy = [(540, 570), (630, 660), (750, 870), (900, 960)]
add_busy_constraints(solver, kimberly_busy)

# Teresa's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 13:00 -> [720, 780)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
teresa_busy = [(540, 570), (600, 690), (720, 780), (900, 930), (990, 1020)]
add_busy_constraints(solver, teresa_busy)

# Dylan's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 12:00 -> [630, 720)
# 13:00 to 15:00 -> [780, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
dylan_busy = [(570, 600), (630, 720), (780, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, dylan_busy)

# Search for the earliest available meeting time that fits everyone's schedule.
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