from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: for a set of busy intervals, ensure the meeting [start, start+duration)
# does not overlap with any interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must be completely before or completely after the busy interval.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Edward's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 15:30 -> [900, 930)
edward_busy = [(540, 630), (750, 780), (810, 840), (900, 930)]
add_busy_constraints(solver, edward_busy)

# Daniel's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 15:00 to 15:30 -> [900, 930)
daniel_busy = [(660, 690), (900, 930)]
add_busy_constraints(solver, daniel_busy)

# Jonathan's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
jonathan_busy = [(540, 630), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, jonathan_busy)

# Samuel's busy intervals:
# 9:30 to 11:30   -> [570, 690)
# 12:00 to 12:30  -> [720, 750)
# 14:00 to 16:30  -> [840, 990)
samuel_busy = [(570, 690), (720, 750), (840, 990)]
add_busy_constraints(solver, samuel_busy)

# Paul's busy intervals:
# 10:00 to 11:00   -> [600, 660)
# 12:30 to 13:00   -> [750, 780)
# 13:30 to 14:00   -> [810, 840)
# 14:30 to 16:00   -> [870, 960)
# 16:30 to 17:00   -> [990, 1020)
paul_busy = [(600, 660), (750, 780), (810, 840), (870, 960), (990, 1020)]
add_busy_constraints(solver, paul_busy)

# Since the group would like to meet at their earliest availability,
# we iterate from 9:00 (540) to the latest valid start time (1020-30=990)
solution_found = False
for t in range(540, 991):
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