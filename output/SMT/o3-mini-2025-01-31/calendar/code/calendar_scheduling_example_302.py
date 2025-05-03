from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Anna prefers not to meet before 14:00 (840 minutes).
solver.add(start >= 840)

# Helper function to add constraints so the meeting does not overlap busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Nicole's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 14:30 to 15:00 -> [870, 900)
nicole_busy = [(600, 630), (870, 900)]
add_busy_constraints(solver, nicole_busy)

# Christine's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
christine_busy = [(660, 690), (750, 780)]
add_busy_constraints(solver, christine_busy)

# Anna's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:30 to 13:00  -> [750, 780)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
anna_busy = [(570, 630), (660, 690), (750, 780), (930, 960), (990, 1020)]
add_busy_constraints(solver, anna_busy)

# Terry's busy intervals:
# 9:30 to 11:30  -> [570, 690)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:30 -> [840, 930)
terry_busy = [(570, 690), (780, 810), (840, 930)]
add_busy_constraints(solver, terry_busy)

# Julie's busy intervals:
# 10:00 to 12:00  -> [600, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 15:00  -> [840, 900)
julie_busy = [(600, 720), (750, 810), (840, 900)]
add_busy_constraints(solver, julie_busy)

# Abigail's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 14:00  -> [750, 840)
# 14:30 to 15:00  -> [870, 900)
# 16:30 to 17:00  -> [990, 1020)
abigail_busy = [(540, 600), (690, 720), (750, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, abigail_busy)

# Try to find the earliest valid meeting time.
found = False
for t in range(840, 1020 - duration + 1):  # starting at 14:00 (840) due to Anna's preference
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")