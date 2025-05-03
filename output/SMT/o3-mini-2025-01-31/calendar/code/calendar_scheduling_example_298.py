from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting does not overlap with any busy interval if it ends
        # before the busy interval starts, or starts after the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Ryan's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
ryan_busy = [(780, 810), (840, 870)]
add_busy_constraints(solver, ryan_busy)

# Randy is free the entire day -- no busy intervals.

# Diana has no meetings the whole day -- no busy intervals.

# Stephanie's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 14:00 -> [660, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:30 -> [930, 990)
stephanie_busy = [(540, 630), (660, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, stephanie_busy)

# Doris's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 13:00 to 14:00 -> [780, 840)
# 14:30 to 16:30 -> [870, 990)
doris_busy = [(540, 570), (600, 690), (780, 840), (870, 990)]
add_busy_constraints(solver, doris_busy)

# Iterate over possible times to find the earliest valid meeting time.
found = False
# t ranges from 9:00 (540) to last possible starting minute such that meeting ends by 17:00.
for t in range(540, 1020 - duration + 1):
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