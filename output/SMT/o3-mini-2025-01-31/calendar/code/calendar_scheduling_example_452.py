from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Given busy intervals as (start, end) in minutes,
# ensure the meeting [start, start+duration) does not overlap any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish before the busy interval starts,
        # or start after (or at) the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Austin is free the entire day, so no constraints.

# Andrew's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
andrew_busy = [(540, 570), (600, 630), (660, 690), (810, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, andrew_busy)

# Raymond's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 16:30 to 17:00 -> [990, 1020)
raymond_busy = [(660, 690), (990, 1020)]
add_busy_constraints(solver, raymond_busy)

# Mary's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:30 -> [690, 750)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
mary_busy = [(540, 570), (600, 630), (690, 750), (930, 960), (990, 1020)]
add_busy_constraints(solver, mary_busy)

# Bobby's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 11:30  -> [660, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 15:30  -> [780, 930)
# 16:00 to 17:00  -> [960, 1020)
bobby_busy = [(570, 600), (660, 690), (720, 750), (780, 930), (960, 1020)]
add_busy_constraints(solver, bobby_busy)

# Shirley's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 16:30  -> [810, 990)
shirley_busy = [(540, 630), (690, 780), (810, 990)]
add_busy_constraints(solver, shirley_busy)

# Jordan's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:30 to 12:00  -> [690, 720)
# 13:00 to 14:30  -> [780, 870)
# 15:30 to 16:30  -> [930, 990)
jordan_busy = [(570, 630), (690, 720), (780, 870), (930, 990)]
add_busy_constraints(solver, jordan_busy)

# Iterate over possible meeting start times (each minute) within work hours.
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