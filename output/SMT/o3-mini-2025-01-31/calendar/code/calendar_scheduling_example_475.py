from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) doesn't overlap the busy period.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Brittany's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:30 -> [870, 930)
brittany_busy = [(600, 630), (720, 750), (870, 930)]
add_busy_constraints(solver, brittany_busy)

# Debra's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
debra_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, debra_busy)

# Amber's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
amber_busy = [(660, 690), (780, 810)]
add_busy_constraints(solver, amber_busy)

# Theresa's busy intervals:
# 14:00 to 14:30 -> [840, 870)
# 16:30 to 17:00 -> [990, 1020)
theresa_busy = [(840, 870), (990, 1020)]
add_busy_constraints(solver, theresa_busy)

# Gloria's busy intervals:
# 10:00 to 13:00 -> [600, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:00 -> [870, 960)
gloria_busy = [(600, 780), (810, 840), (870, 960)]
add_busy_constraints(solver, gloria_busy)

# Amanda's busy intervals:
# 9:00 to 10:30 -> [540, 630)
# 11:00 to 14:00 -> [660, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
amanda_busy = [(540, 630), (660, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, amanda_busy)

# Stephanie's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
stephanie_busy = [(540, 570), (600, 690), (720, 810), (840, 870), (900, 960)]
add_busy_constraints(solver, stephanie_busy)

# Search for the earliest available meeting time.
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
        solver.pop()  # pop for the valid solution
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")