from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [busy_start, busy_end), the meeting interval
# [start, start+duration) must either finish before busy_start or start at/after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))
        
# Walter is free all day, so no constraints.

# Frances is free all day, so no constraints.

# Martha's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
martha_busy = [(540, 570), (630, 660), (750, 780), (810, 840)]
add_busy_constraints(solver, martha_busy)

# Lori is free all day.

# Beverly's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:30 to 15:00  -> [750, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
beverly_busy = [(540, 600), (630, 660), (750, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, beverly_busy)

# Christine's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 16:00  -> [870, 960)
# 16:30 to 17:00  -> [990, 1020)
christine_busy = [(540, 660), (690, 750), (780, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, christine_busy)

# Catherine's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:00  -> [780, 840)
# 15:00 to 17:00  -> [900, 1020)
catherine_busy = [(540, 630), (690, 720), (780, 840), (900, 1020)]
add_busy_constraints(solver, catherine_busy)

# Search for a valid meeting start time by iterating over each possible time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}.".format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")