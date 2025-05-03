from z3 import Solver, Int, Or, sat

# Create a new Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, intervals):
    for bstart, bend in intervals:
        # The meeting [start, start+duration) must either finish 
        # before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= bstart, start >= bend))

# Kyle's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 15:00 -> [840, 900)
kyle_busy = [(570, 600), (750, 780), (840, 900)]
add_busy_constraints(solver, kyle_busy)

# Danielle is free the entire day (no constraints).

# Kelly's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 12:30 -> [720, 750)
kelly_busy = [(600, 630), (720, 750)]
add_busy_constraints(solver, kelly_busy)

# Carol is free the entire day (no constraints).

# Angela's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 13:00  -> [720, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
angela_busy = [(540, 600), (630, 690), (720, 780), (810, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, angela_busy)

# Carolyn's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 15:30 -> [810, 930)
carolyn_busy = [(570, 600), (690, 780), (810, 930)]
add_busy_constraints(solver, carolyn_busy)

# Gary's busy intervals:
# 9:00 to 15:30  -> [540, 930)
# 16:30 to 17:00 -> [990, 1020)
gary_busy = [(540, 930), (990, 1020)]
add_busy_constraints(solver, gary_busy)

# Search for the earliest start time that satisfies all constraints.
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