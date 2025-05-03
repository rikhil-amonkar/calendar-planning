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

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any provided busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval starts, or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Walter has no meetings the whole day.
# Cynthia's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 16:00 -> [900, 960)
cynthia_busy = [(540, 570), (600, 630), (810, 870), (900, 960)]
add_busy_constraints(solver, cynthia_busy)

# Ann's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
# 16:00 to 16:30 -> [960, 990)
ann_busy = [(600, 660), (780, 810), (840, 900), (960, 990)]
add_busy_constraints(solver, ann_busy)

# Catherine's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:30 to 13:30  -> [750, 810)
# 14:30 to 17:00  -> [870, 1020)
catherine_busy = [(540, 690), (750, 810), (870, 1020)]
add_busy_constraints(solver, catherine_busy)

# Kyle's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 16:00 -> [900, 960)
kyle_busy = [(540, 570), (600, 690), (720, 750), (780, 870), (900, 960)]
add_busy_constraints(solver, kyle_busy)

# Since we want the earliest slot that works for everyone,
# iterate over possible start times (from 9:00 to latest start time)
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")