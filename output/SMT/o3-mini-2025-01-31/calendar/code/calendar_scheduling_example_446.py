from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 min) to 17:00 (1020 min)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For each busy interval [busy_start, busy_end),
# the meeting interval [start, start+duration) must either end before busy_start
# or start on/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Megan's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 12:00 to 12:30 -> [720, 750)
megan_busy = [(540, 570), (600, 660), (720, 750)]
add_busy_constraints(solver, megan_busy)

# Christine's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:00  -> [780, 840)
# 15:30 to 16:30  -> [930, 990)
christine_busy = [(540, 570), (690, 720), (780, 840), (930, 990)]
add_busy_constraints(solver, christine_busy)

# Gabriel is free all day; no busy intervals.

# Sara's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:00 -> [870, 900)
sara_busy = [(690, 720), (870, 900)]
add_busy_constraints(solver, sara_busy)

# Bruce's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 14:00  -> [750, 840)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:30  -> [930, 990)
bruce_busy = [(570, 600), (630, 720), (750, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, bruce_busy)

# Kathryn's busy intervals:
# 10:00 to 15:30 -> [600, 930)
# 16:00 to 16:30 -> [960, 990)
kathryn_busy = [(600, 930), (960, 990)]
add_busy_constraints(solver, kathryn_busy)

# Billy's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 14:00  -> [720, 840)
# 14:30 to 15:30  -> [870, 930)
billy_busy = [(540, 570), (660, 690), (720, 840), (870, 930)]
add_busy_constraints(solver, billy_busy)

# Search for a valid meeting start time by iterating through possible minutes.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")