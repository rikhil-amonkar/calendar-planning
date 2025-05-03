from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional preference:
# Beverly would like to avoid meetings on Monday before 11:30.
# We enforce the meeting to start no earlier than 11:30 (690 minutes).
solver.add(start >= 690)

# Helper function to add constraints ensuring that the meeting [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval begins or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Nicholas has no meetings (no constraints).

# Robert's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
robert_busy = [(750, 780), (810, 840)]
add_busy_constraints(solver, robert_busy)

# Gary's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 13:00 to 13:30 -> [780, 810)
gary_busy = [(540, 570), (780, 810)]
add_busy_constraints(solver, gary_busy)

# Doris's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 13:30 -> [690, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
doris_busy = [(540, 570), (600, 660), (690, 810), (840, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, doris_busy)

# Beverly's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 14:00 -> [600, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:30 -> [930, 990)
beverly_busy = [(540, 570), (600, 840), (870, 900), (930, 990)]
add_busy_constraints(solver, beverly_busy)

# Search for the earliest valid meeting start time.
solution_found = False
for t in range(690, 1020 - duration + 1):  # start from 11:30 (690 minutes)
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")