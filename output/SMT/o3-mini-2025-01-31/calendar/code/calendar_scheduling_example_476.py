from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Roger's preference: do not meet before 12:30 (i.e. before 750 minutes)
solver.add(start >= 750)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either end before the busy interval 
        # begins, or start after it ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Daniel: no meetings (free all day), so no busy intervals.

# Kathleen is busy on Monday during 14:30 to 15:30 -> [870, 930)
kathleen_busy = [(870, 930)]
add_busy_constraints(solver, kathleen_busy)

# Carolyn is busy on Monday during 12:00 to 12:30 and 13:00 to 13:30 -> [720,750) and [780,810)
carolyn_busy = [(720, 750), (780, 810)]
add_busy_constraints(solver, carolyn_busy)

# Roger is free the entire day; his preference is already added.

# Cheryl is busy on Monday during:
# 9:00 to 9:30 -> [540,570),
# 10:00 to 11:30 -> [600,690),
# 12:30 to 13:30 -> [750,810),
# 14:00 to 17:00 -> [840,1020)
cheryl_busy = [(540, 570), (600, 690), (750, 810), (840, 1020)]
add_busy_constraints(solver, cheryl_busy)

# Virginia is busy on Monday during:
# 9:30 to 11:30 -> [570,690),
# 12:00 to 12:30 -> [720,750),
# 13:00 to 13:30 -> [780,810),
# 14:30 to 15:30 -> [870,930),
# 16:00 to 17:00 -> [960,1020)
virginia_busy = [(570, 690), (720, 750), (780, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, virginia_busy)

# Angela is busy on Monday during:
# 9:30 to 10:00 -> [570,600),
# 10:30 to 11:30 -> [630,690),
# 12:00 to 12:30 -> [720,750),
# 13:00 to 13:30 -> [780,810),
# 14:00 to 16:30 -> [840,990)
angela_busy = [(570, 600), (630, 690), (720, 750), (780, 810), (840, 990)]
add_busy_constraints(solver, angela_busy)

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
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")